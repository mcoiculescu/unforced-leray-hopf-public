import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_1_2_1_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Sub.RingLiftOffAxis_Sub.HeatFieldJet

/-!
# Shared heat-lift and `JQIndep` helpers for `PartIII-b:C/ward/12/3/2/2/1/2/1/2/1..3`

Provides:
1. `WtdLineJetBdd` and `WtdHeatJet2Bdd`: weighted 1D Gaussian derivative bounds and 3D Cartesian
   second-jet bounds `(1 + y 2 ^ 2) ‖D² F(y)‖ ≤ C` on `Axi.ϱ y ≤ R` for lifted heat terms.
2. Off-axis lift formulas (`lhP_chartSwap_chart`, `lift_radial_lhP`, `lift_axial_lhP`,
   `lift_radial_lhP_mul`) expressing `Axi.age R z • Axi.Nv R (...) τ z` on `lhP` profiles and their
   quadratic products as explicit smooth fields in `(z 0 ^ 2 + z 1 ^ 2)^d * g_ν^{(m)}(z 2)`.
3. `JQIndep a F`: `q`-independent families in `Jet.JQ n a` for all `n`, closed under linear
   combinations, products, `K`, `∂_η`, `ageShift`, and `famNu`, together with the finite-order
   mean-stream decomposition `meanFam = heatSumFam M + remFam M` and the late directional-partial
   bound `jqIndep_late_partials_bound`.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.PhaseSpace MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal BigOperators
open UnforcedLeray.Cons.C03.Concrete (Params)
open UnforcedLeray.Short.IIb (trainStream trainPressure)
open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0187 UnforcedLeray.B0188
  UnforcedLeray.B0190 UnforcedLeray.Short.PartIIa
open UnforcedLeray.Short.PartI

namespace UnforcedLeray.Short.PartIIIb.Concrete

open FarDecaySub EarlyJet2Sub

namespace LateHeatDecomp2Sub

/-! ### Part 1: Weighted 1D Gaussian jets and 3D lifted heat-field second jets -/

/-- A 1D profile `P : ℝ → ℝ` is `C^∞` and all its derivatives have bounded `(1 + z²)`-weighted
supremum norm on `ℝ`. -/
def WtdLineJetBdd (P : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ P ∧ ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ,
    (1 + z ^ 2) * ‖iteratedFDeriv ℝ k P z‖ ≤ C

/-- Pointwise `(1 + z²)`-weighted bound on `B0191.profileDeriv ν n`. -/
theorem wtd_profileDeriv_bdd {ν : ℝ} (hν : 0 < ν) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, (1 + z ^ 2) * |UnforcedLeray.B0191.profileDeriv ν n z| ≤ C := by
  obtain ⟨Q, hQ⟩ := lhPoly n
  obtain ⟨B, hB0, hB⟩ := lhPolyGauss Q 1
  set A : ℝ := (Real.sqrt (4 * Real.pi * ν))⁻¹ * (Real.sqrt ν)⁻¹ ^ n
  have hA0 : 0 ≤ A := by unfold A; positivity
  refine ⟨(1 + ν) * A * B, by positivity, fun z => ?_⟩
  have hpd : UnforcedLeray.B0191.profileDeriv ν n z = iteratedDeriv n (heatKernel1 (ν * 1)) z := by
    have h := lhHeatKernelEq ν n z 1
    exact h
  rw [hpd, mul_one, hQ ν hν z]
  set u : ℝ := z / Real.sqrt ν
  have hu2 : z ^ 2 = ν * u ^ 2 := by
    dsimp [u]
    rw [div_pow, Real.sq_sqrt hν.le, mul_div_cancel₀ _ hν.ne']
  have hexp_eq : -(z ^ 2) / (4 * ν) = -(u ^ 2 / 4) := by
    rw [hu2]
    have hνne : ν ≠ 0 := hν.ne'
    field_simp
  have h1z : 1 + z ^ 2 ≤ (1 + ν) * (1 + u ^ 2) ^ 1 := by
    rw [hu2, pow_one]
    nlinarith [sq_nonneg u]
  have habs : |A * Q.eval u * Real.exp (-(z ^ 2) / (4 * ν))| =
      A * |Q.eval u| * Real.exp (-(u ^ 2 / 4)) := by
    rw [hexp_eq, abs_mul, abs_mul, abs_of_nonneg hA0, abs_of_pos (Real.exp_pos _)]
  change (1 + z ^ 2) * |A * Q.eval u * Real.exp (-(z ^ 2) / (4 * ν))| ≤ (1 + ν) * A * B
  rw [habs]
  have hBu := hB u
  calc (1 + z ^ 2) * (A * |Q.eval u| * Real.exp (-(u ^ 2 / 4)))
      ≤ ((1 + ν) * (1 + u ^ 2) ^ 1) * (A * |Q.eval u| * Real.exp (-(u ^ 2 / 4))) :=
        mul_le_mul_of_nonneg_right h1z (by positivity)
    _ = (1 + ν) * A * ((1 + u ^ 2) ^ 1 * |Q.eval u| * Real.exp (-(u ^ 2 / 4))) := by ring
    _ ≤ (1 + ν) * A * B := mul_le_mul_of_nonneg_left hBu (by positivity)

/-- Every derivative `B0191.profileDeriv ν m` satisfies `WtdLineJetBdd` for `0 < ν`. -/
theorem wtdLineJetBdd_profileDeriv {ν : ℝ} (hν : 0 < ν) (m : ℕ) :
    WtdLineJetBdd (UnforcedLeray.B0191.profileDeriv ν m) := by
  refine ⟨UnforcedLeray.Short.IIb.contDiff_profileDeriv ν m, fun k => ?_⟩
  obtain ⟨C, hC0, hC⟩ := wtd_profileDeriv_bdd hν (m + k)
  refine ⟨C, hC0, fun z => ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hfjProfileDerivEq ν k m, Real.norm_eq_abs]
  exact hC z

/-- `WtdLineJetBdd` is closed under pointwise multiplication. -/
theorem wtdLineJetBdd_mul {P₁ P₂ : ℝ → ℝ} (h₁ : WtdLineJetBdd P₁) (h₂ : WtdLineJetBdd P₂) :
    WtdLineJetBdd (fun z => P₁ z * P₂ z) := by
  refine ⟨h₁.1.mul h₂.1, fun k => ?_⟩
  choose C₁ hC₁0 hC₁ using h₁.2
  choose C₂ hC₂0 hC₂ using h₂.2
  refine ⟨∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * C₁ i * C₂ (k - i),
    Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC₁0 i)) (hC₂0 _),
    fun z => ?_⟩
  have hle := norm_iteratedFDeriv_mul_le (n := k) h₁.1 h₂.1 z (by exact_mod_cast le_top)
  have hw0 : 0 ≤ 1 + z ^ 2 := by positivity
  have hw1 : 1 ≤ 1 + z ^ 2 := by linarith [sq_nonneg z]
  calc (1 + z ^ 2) * ‖iteratedFDeriv ℝ k (fun w => P₁ w * P₂ w) z‖
      ≤ (1 + z ^ 2) * ∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i P₁ z‖ * ‖iteratedFDeriv ℝ (k - i) P₂ z‖ :=
        mul_le_mul_of_nonneg_left hle hw0
    _ = ∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ) * ((1 + z ^ 2) * ‖iteratedFDeriv ℝ i P₁ z‖) *
            ‖iteratedFDeriv ℝ (k - i) P₂ z‖ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring
    _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * C₁ i * C₂ (k - i) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h2 : ‖iteratedFDeriv ℝ (k - i) P₂ z‖ ≤ C₂ (k - i) := by
          calc ‖iteratedFDeriv ℝ (k - i) P₂ z‖
              = 1 * ‖iteratedFDeriv ℝ (k - i) P₂ z‖ := (one_mul _).symm
            _ ≤ (1 + z ^ 2) * ‖iteratedFDeriv ℝ (k - i) P₂ z‖ :=
                mul_le_mul_of_nonneg_right hw1 (norm_nonneg _)
            _ ≤ C₂ (k - i) := hC₂ (k - i) z
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hC₁ i z) (Nat.cast_nonneg _)) h2
          (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hC₁0 i))

/-- A 3D vector field `F : Space → Space` is `C^∞` and has bounded `(1 + y 2 ^ 2)`-weighted second
Fréchet derivative on the cylinder `Axi.ϱ y ≤ R`. -/
def WtdHeatJet2Bdd (R : ℝ) (F : Space → Space) : Prop :=
  ContDiff ℝ ∞ F ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Space, Axi.ϱ y ≤ R →
    (1 + y 2 ^ 2) * ‖iteratedFDeriv ℝ 2 F y‖ ≤ C

theorem wtdHeatJet2Bdd_zero (R : ℝ) : WtdHeatJet2Bdd R (fun _ => 0) := by
  refine ⟨contDiff_const, 0, le_rfl, fun y _ => ?_⟩
  rw [iteratedFDeriv_const_of_ne (by norm_num : (2 : ℕ) ≠ 0) (0 : Space)]
  simp

theorem wtdHeatJet2Bdd_add {R : ℝ} {F₁ F₂ : Space → Space}
    (h₁ : WtdHeatJet2Bdd R F₁) (h₂ : WtdHeatJet2Bdd R F₂) :
    WtdHeatJet2Bdd R (fun y => F₁ y + F₂ y) := by
  obtain ⟨c₁, C₁, hC₁0, hB₁⟩ := h₁
  obtain ⟨c₂, C₂, hC₂0, hB₂⟩ := h₂
  refine ⟨c₁.add c₂, C₁ + C₂, add_nonneg hC₁0 hC₂0, fun y hy => ?_⟩
  have hadd : iteratedFDeriv ℝ 2 (fun z => F₁ z + F₂ z) y =
      iteratedFDeriv ℝ 2 F₁ y + iteratedFDeriv ℝ 2 F₂ y :=
    iteratedFDeriv_add_apply (c₁.contDiffAt.of_le (by norm_num))
      (c₂.contDiffAt.of_le (by norm_num))
  have hw0 : 0 ≤ 1 + y 2 ^ 2 := by positivity
  have hnorm : ‖iteratedFDeriv ℝ 2 (fun z => F₁ z + F₂ z) y‖ ≤
      ‖iteratedFDeriv ℝ 2 F₁ y‖ + ‖iteratedFDeriv ℝ 2 F₂ y‖ := by
    rw [hadd]; exact norm_add_le _ _
  have hmul := mul_le_mul_of_nonneg_left hnorm hw0
  linarith [hB₁ y hy, hB₂ y hy]

theorem wtdHeatJet2Bdd_sum {R : ℝ} {ι : Type*} [DecidableEq ι] (s : Finset ι)
    {F : ι → Space → Space} (h : ∀ i ∈ s, WtdHeatJet2Bdd R (F i)) :
    WtdHeatJet2Bdd R (fun y => ∑ i ∈ s, F i y) := by
  induction s using Finset.induction_on with
  | empty =>
    simpa using wtdHeatJet2Bdd_zero R
  | @insert a s ha ih =>
    have heq : (fun y : Space => ∑ i ∈ insert a s, F i y) =
        fun y => F a y + ∑ i ∈ s, F i y := by
      funext y
      exact Finset.sum_insert ha
    rw [heq]
    exact wtdHeatJet2Bdd_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Core weighted second-jet bound for a separable product `(a y * P (y 2)) • v`. -/
theorem wtdHeatJet2Bdd_smul_const {R : ℝ} (_hR : 0 ≤ R) {a : Space → ℝ}
    (ha : ContDiff ℝ ∞ a) (Ha : HeatJetBdd (R ^ 2) a) {P : ℝ → ℝ} (hP : WtdLineJetBdd P)
    (v : Space) :
    WtdHeatJet2Bdd R (fun y : Space => (a y * P (y 2)) • v) := by
  set π₂ : Space →L[ℝ] ℝ := EuclideanSpace.proj 2
  set B : Space → ℝ := fun y => P (y 2)
  have hB_eq : B = P ∘ π₂ := rfl
  have cB : ContDiff ℝ ∞ B := hP.1.comp π₂.contDiff
  set f : Space → ℝ := fun y => a y * B y
  have cf : ContDiff ℝ ∞ f := ha.mul cB
  set L : ℝ →L[ℝ] Space := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  have hF_eq : (fun y : Space => (a y * P (y 2)) • v) = L ∘ f := rfl
  have cF : ContDiff ℝ ∞ (fun y : Space => (a y * P (y 2)) • v) := cf.smul contDiff_const
  choose Ca hCa0 hCa using Ha
  choose CP hCP0 hCP using hP.2
  set C_f : ℝ :=
    ∑ i ∈ Finset.range 3, (Nat.choose 2 i : ℝ) * Ca i * (CP (2 - i) * ‖π₂‖ ^ (2 - i))
  have hCf0 : 0 ≤ C_f := by
    unfold C_f
    refine Finset.sum_nonneg fun i _ => ?_
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCa0 i))
      (mul_nonneg (hCP0 _) (pow_nonneg (norm_nonneg _) _))
  refine ⟨cF, ‖L‖ * C_f, mul_nonneg (norm_nonneg _) hCf0, fun y hy => ?_⟩
  have hy2 : Axi.ϱ y ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (Axi.ϱ_nonneg y) hy 2
  have hw0 : 0 ≤ 1 + y 2 ^ 2 := by positivity
  have hB_jet : ∀ j : ℕ, (1 + y 2 ^ 2) * ‖iteratedFDeriv ℝ j B y‖ ≤ CP j * ‖π₂‖ ^ j := by
    intro j
    rw [hB_eq, ContinuousLinearMap.iteratedFDeriv_comp_right π₂ hP.1 y (by exact_mod_cast le_top)]
    have hcomp := (ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv ℝ j P (π₂ y)) (fun _ => π₂))
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hcomp
    calc (1 + y 2 ^ 2) *
          ‖(iteratedFDeriv ℝ j P (π₂ y)).compContinuousLinearMap fun _ => π₂‖
        ≤ (1 + y 2 ^ 2) * (‖iteratedFDeriv ℝ j P (y 2)‖ * ‖π₂‖ ^ j) :=
          mul_le_mul_of_nonneg_left hcomp hw0
      _ = ((1 + y 2 ^ 2) * ‖iteratedFDeriv ℝ j P (y 2)‖) * ‖π₂‖ ^ j := by ring
      _ ≤ CP j * ‖π₂‖ ^ j :=
          mul_le_mul_of_nonneg_right (hCP j (y 2)) (pow_nonneg (norm_nonneg _) _)
  have hf_le : (1 + y 2 ^ 2) * ‖iteratedFDeriv ℝ 2 f y‖ ≤ C_f := by
    have hmul := norm_iteratedFDeriv_mul_le (n := 2) ha cB y (by norm_num)
    calc (1 + y 2 ^ 2) * ‖iteratedFDeriv ℝ 2 f y‖
        ≤ (1 + y 2 ^ 2) * ∑ i ∈ Finset.range 3,
            (Nat.choose 2 i : ℝ) * ‖iteratedFDeriv ℝ i a y‖ * ‖iteratedFDeriv ℝ (2 - i) B y‖ :=
          mul_le_mul_of_nonneg_left hmul hw0
      _ = ∑ i ∈ Finset.range 3,
            (Nat.choose 2 i : ℝ) * ‖iteratedFDeriv ℝ i a y‖ *
              ((1 + y 2 ^ 2) * ‖iteratedFDeriv ℝ (2 - i) B y‖) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => by ring
      _ ≤ C_f := by
          unfold C_f
          refine Finset.sum_le_sum fun i _ => ?_
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left (hCa i y hy2) (Nat.cast_nonneg _))
            (hB_jet (2 - i))
            (mul_nonneg hw0 (norm_nonneg _))
            (mul_nonneg (Nat.cast_nonneg _) (hCa0 i))
  have hL_le : ‖iteratedFDeriv ℝ 2 (fun z : Space => (a z * P (z 2)) • v) y‖ ≤
      ‖L‖ * ‖iteratedFDeriv ℝ 2 f y‖ := by
    rw [hF_eq]
    exact L.norm_iteratedFDeriv_comp_left cf.contDiffAt (by norm_num)
  calc (1 + y 2 ^ 2) * ‖iteratedFDeriv ℝ 2 (fun z : Space => (a z * P (z 2)) • v) y‖
      ≤ (1 + y 2 ^ 2) * (‖L‖ * ‖iteratedFDeriv ℝ 2 f y‖) :=
        mul_le_mul_of_nonneg_left hL_le hw0
    _ = ‖L‖ * ((1 + y 2 ^ 2) * ‖iteratedFDeriv ℝ 2 f y‖) := by ring
    _ ≤ ‖L‖ * C_f := mul_le_mul_of_nonneg_left hf_le (norm_nonneg _)

theorem hfj_poly_w (W c : ℝ) (d : ℕ) :
    ContDiff ℝ ∞ (fun y : Space => c * (y 0 ^ 2 + y 1 ^ 2) ^ d) ∧
      HeatJetBdd W (fun y : Space => c * (y 0 ^ 2 + y 1 ^ 2) ^ d) := by
  have c0 : ContDiff ℝ ∞ (fun y : Space => y 0) := by fun_prop
  have c1 : ContDiff ℝ ∞ (fun y : Space => y 1) := by fun_prop
  have cw : ContDiff ℝ ∞ (fun y : Space => y 0 ^ 2 + y 1 ^ 2) := by fun_prop
  have h0 : HeatJetBdd W (fun y : Space => y 0) :=
    hfjCoord (W := W) 0 (fun y => le_add_of_nonneg_right (sq_nonneg _))
  have h1 : HeatJetBdd W (fun y : Space => y 1) :=
    hfjCoord (W := W) 1 (fun y => le_add_of_nonneg_left (sq_nonneg _))
  have hw : HeatJetBdd W (fun y : Space => y 0 ^ 2 + y 1 ^ 2) :=
    hfjAdd (f := fun y : Space => y 0 ^ 2) (g := fun y : Space => y 1 ^ 2)
      (by fun_prop) (by fun_prop) (hfjPow c0 h0 2) (hfjPow c1 h1 2)
  have hwd : HeatJetBdd W (fun y : Space => (y 0 ^ 2 + y 1 ^ 2) ^ d) := hfjPow cw hw d
  exact ⟨contDiff_const.mul (cw.pow d),
    hfjMul contDiff_const (cw.pow d) (hfjConst c) hwd⟩

/-- `WtdHeatJet2Bdd R` for an axial heat term `(c * (y 0 ^ 2 + y 1 ^ 2)^d * P (y 2)) • Axi.e3`. -/
theorem wtdHeatJet2Bdd_e3 {R : ℝ} (hR : 0 ≤ R) (c : ℝ) (d : ℕ) {P : ℝ → ℝ}
    (hP : WtdLineJetBdd P) :
    WtdHeatJet2Bdd R (fun y : Space => (c * (y 0 ^ 2 + y 1 ^ 2) ^ d * P (y 2)) • Axi.e3) := by
  obtain ⟨ca, Ha⟩ := hfj_poly_w (R ^ 2) c d
  exact wtdHeatJet2Bdd_smul_const hR ca Ha hP Axi.e3

/-- `WtdHeatJet2Bdd R` for a radial heat term `(c * (y 0 ^ 2 + y 1 ^ 2)^d * P (y 2)) • Axi.hor y`. -/
theorem wtdHeatJet2Bdd_hor {R : ℝ} (hR : 0 ≤ R) (c : ℝ) (d : ℕ) {P : ℝ → ℝ}
    (hP : WtdLineJetBdd P) :
    WtdHeatJet2Bdd R (fun y : Space => (c * (y 0 ^ 2 + y 1 ^ 2) ^ d * P (y 2)) • Axi.hor y) := by
  obtain ⟨ca, Ha⟩ := hfj_poly_w (R ^ 2) c d
  have c0 : ContDiff ℝ ∞ (fun y : Space => y 0) := by fun_prop
  have c1 : ContDiff ℝ ∞ (fun y : Space => y 1) := by fun_prop
  have h0 : HeatJetBdd (R ^ 2) (fun y : Space => y 0) :=
    hfjCoord (W := R ^ 2) 0 (fun y => le_add_of_nonneg_right (sq_nonneg _))
  have h1 : HeatJetBdd (R ^ 2) (fun y : Space => y 1) :=
    hfjCoord (W := R ^ 2) 1 (fun y => le_add_of_nonneg_left (sq_nonneg _))
  have hT0 := wtdHeatJet2Bdd_smul_const hR (ca.mul c0) (hfjMul ca c0 Ha h0) hP
    (UnforcedLeray.coordinateVector 0)
  have hT1 := wtdHeatJet2Bdd_smul_const hR (ca.mul c1) (hfjMul ca c1 Ha h1) hP
    (UnforcedLeray.coordinateVector 1)
  have heq : (fun y : Space => (c * (y 0 ^ 2 + y 1 ^ 2) ^ d * P (y 2)) • Axi.hor y) =
      fun y : Space =>
        ((c * (y 0 ^ 2 + y 1 ^ 2) ^ d * y 0) * P (y 2)) •
            UnforcedLeray.coordinateVector 0 +
          ((c * (y 0 ^ 2 + y 1 ^ 2) ^ d * y 1) * P (y 2)) •
            UnforcedLeray.coordinateVector 1 := by
    funext y
    have hh : Axi.hor y =
        y 0 • UnforcedLeray.coordinateVector 0 +
          y 1 • UnforcedLeray.coordinateVector 1 := by
      ext i
      fin_cases i <;> simp [Axi.hor, UnforcedLeray.coordinateVector]
    rw [hh]
    module
  rw [heq]
  exact wtdHeatJet2Bdd_add hT0 hT1

/-! ### Part 2: Off-axis lift identities for `lhP` profiles -/

theorem Nv_add_merid (R : ℝ) (g₁ g₂ : ProfilePoint → ℝ) (v : Axi.Merid) (τ : ℝ) (z : Space) :
    Axi.Nv R (fun m => (g₁ (chartSwap m) + g₂ (chartSwap m)) • v) τ z =
      Axi.Nv R (fun m => g₁ (chartSwap m) • v) τ z +
        Axi.Nv R (fun m => g₂ (chartSwap m) • v) τ z := by
  simp only [Axi.Nv, add_smul, map_add, smul_add]

theorem Nv_sum_merid {ι : Type*} [DecidableEq ι] (s : Finset ι) (R : ℝ)
    (g : ι → ProfilePoint → ℝ) (v : Axi.Merid) (τ : ℝ) (z : Space) :
    Axi.Nv R (fun m => (∑ i ∈ s, g i (chartSwap m)) • v) τ z =
      ∑ i ∈ s, Axi.Nv R (fun m => g i (chartSwap m) • v) τ z := by
  induction s using Finset.induction_on with
  | empty =>
    simp [Axi.Nv]
  | @insert a s ha ih =>
    have heq : (fun m : ℝ × (ℝ × ℝ) => (∑ i ∈ insert a s, g i (chartSwap m)) • v) =
        fun m => (g a (chartSwap m) + (fun x => ∑ i ∈ s, g i x) (chartSwap m)) • v := by
      funext m
      rw [Finset.sum_insert ha]
    rw [heq, Nv_add_merid R (g a) (fun x => ∑ i ∈ s, g i x) v τ z, ih, Finset.sum_insert ha]

/-- Self-similarity of `lhP ν k` at the off-axis chart point `chartSwap (Axi.chart R τ z)`. -/
theorem lhP_chartSwap_chart {R : ℝ} (hR : 0 < R) (ν : ℝ) (k : ℕ) (τ : ℝ)
    {z : Space} (hz : z ∉ Axi.axis) :
    lhP ν k (chartSwap (Axi.chart R τ z)) =
      (Axi.ϱ z / R) ^ (k + 1) * UnforcedLeray.B0191.profileDeriv ν k (z 2) := by
  have hρ : 0 < Axi.ϱ z := Axi.ϱ_pos hz
  have hs : 0 < Axi.age R z := age_pos_of hR hz
  have hss := UnforcedLeray.B0191.heatDeriv_selfSimilar ν k (Axi.trans R z) hs
  have hsq : Real.sqrt (Axi.age R z) = R / Axi.ϱ z := Axi.sqrt_age hR hz
  have hinv : (Real.sqrt (Axi.age R z))⁻¹ = Axi.ϱ z / R := by rw [hsq, inv_div]
  have harg : (Real.sqrt (Axi.age R z))⁻¹ * Axi.trans R z = z 2 := by
    rw [hinv]
    unfold Axi.trans
    have hRne : R ≠ 0 := hR.ne'
    have hρne : Axi.ϱ z ≠ 0 := hρ.ne'
    field_simp
  show UnforcedLeray.B0191.heatDeriv ν k (Axi.trans R z) (Axi.age R z) = _
  rw [hss, harg, hinv]

/-- Off-axis lift along `meridE0` of a scalar profile `g`. -/
theorem age_smul_Nv_meridE0 {R : ℝ} (hR : 0 < R) (g : ProfilePoint → ℝ) (τ : ℝ)
    {z : Space} (hz : z ∉ Axi.axis) :
    Axi.age R z • Axi.Nv R (fun m => g (chartSwap m) • meridE0) τ z =
      (Axi.age R z * (R / (z 0 ^ 2 + z 1 ^ 2) * g (chartSwap (Axi.chart R τ z)))) • Axi.hor z := by
  rw [UnforcedLeray.Short.IIb.Nv_eq_parity hR _ τ hz]
  simp only [UnforcedLeray.Short.IIb.parG, UnforcedLeray.Short.IIb.parH, meridE0]
  rw [← UnforcedLeray.Short.IIb.chart_eq_parChart]
  simp [smul_smul]

/-- Off-axis lift along `meridE1` of a scalar profile `g`. -/
theorem age_smul_Nv_meridE1 {R : ℝ} (hR : 0 < R) (g : ProfilePoint → ℝ) (τ : ℝ)
    {z : Space} (hz : z ∉ Axi.axis) :
    Axi.age R z • Axi.Nv R (fun m => g (chartSwap m) • meridE1) τ z =
      (Axi.age R z * (R / Axi.ϱ z * g (chartSwap (Axi.chart R τ z)))) • Axi.e3 := by
  rw [UnforcedLeray.Short.IIb.Nv_eq_parity hR _ τ hz]
  simp only [UnforcedLeray.Short.IIb.parG, UnforcedLeray.Short.IIb.parH, meridE1]
  rw [← UnforcedLeray.Short.IIb.chart_eq_parChart]
  have hsq : Real.sqrt (z 0 ^ 2 + z 1 ^ 2) = Axi.ϱ z := rfl
  rw [hsq]
  simp [smul_smul]

/-- Off-axis radial lift of `c * lhP ν (2 * d + 3)` along `meridE0`. -/
theorem lift_radial_lhP {R : ℝ} (hR : 0 < R) (ν c : ℝ) (d : ℕ) (τ : ℝ)
    {z : Space} (hz : z ∉ Axi.axis) :
    Axi.age R z •
        Axi.Nv R (fun m => (c * lhP ν (2 * d + 3) (chartSwap m)) • meridE0) τ z =
      ((c / R ^ (2 * d + 1)) * (z 0 ^ 2 + z 1 ^ 2) ^ d *
        UnforcedLeray.B0191.profileDeriv ν (2 * d + 3) (z 2)) • Axi.hor z := by
  rw [age_smul_Nv_meridE0 hR (fun x => c * lhP ν (2 * d + 3) x) τ hz,
    lhP_chartSwap_chart hR ν (2 * d + 3) τ hz]
  congr 1
  have hρ : 0 < Axi.ϱ z := Axi.ϱ_pos hz
  have hρne : Axi.ϱ z ≠ 0 := hρ.ne'
  have hRne : R ≠ 0 := hR.ne'
  have hw : z 0 ^ 2 + z 1 ^ 2 = Axi.ϱ z ^ 2 := (Axi.ϱ_sq z).symm
  have hpow : Axi.ϱ z ^ (2 * d + 3 + 1) = (Axi.ϱ z ^ 2) ^ d * (Axi.ϱ z ^ 2) ^ 2 := by ring
  have hRpow : R ^ (2 * d + 3 + 1) = R ^ (2 * d + 1) * R ^ 3 := by ring
  unfold Axi.age
  rw [hw, div_pow, hpow, hRpow]
  field_simp

/-- Off-axis axial lift of `c * lhP ν (2 * d + 2)` along `meridE1`. -/
theorem lift_axial_lhP {R : ℝ} (hR : 0 < R) (ν c : ℝ) (d : ℕ) (τ : ℝ)
    {z : Space} (hz : z ∉ Axi.axis) :
    Axi.age R z •
        Axi.Nv R (fun m => (c * lhP ν (2 * d + 2) (chartSwap m)) • meridE1) τ z =
      ((c / R ^ (2 * d)) * (z 0 ^ 2 + z 1 ^ 2) ^ d *
        UnforcedLeray.B0191.profileDeriv ν (2 * d + 2) (z 2)) • Axi.e3 := by
  rw [age_smul_Nv_meridE1 hR (fun x => c * lhP ν (2 * d + 2) x) τ hz,
    lhP_chartSwap_chart hR ν (2 * d + 2) τ hz]
  congr 1
  have hρ : 0 < Axi.ϱ z := Axi.ϱ_pos hz
  have hρne : Axi.ϱ z ≠ 0 := hρ.ne'
  have hRne : R ≠ 0 := hR.ne'
  have hw : z 0 ^ 2 + z 1 ^ 2 = Axi.ϱ z ^ 2 := (Axi.ϱ_sq z).symm
  have hpow : Axi.ϱ z ^ (2 * d + 2 + 1) = (Axi.ϱ z ^ 2) ^ d * Axi.ϱ z ^ 3 := by ring
  have hRpow : R ^ (2 * d + 2 + 1) = R ^ (2 * d) * R ^ 3 := by ring
  unfold Axi.age
  rw [hw, div_pow, hpow, hRpow]
  field_simp

/-- Off-axis radial lift of a product `c * (lhP ν m₁ * lhP ν m₂)` with
`(m₁ + 1) + (m₂ + 1) = 2 * d + 4` along `meridE0`. -/
theorem lift_radial_lhP_mul {R : ℝ} (hR : 0 < R) (ν c : ℝ) {d m₁ m₂ : ℕ}
    (hm : (m₁ + 1) + (m₂ + 1) = 2 * d + 4) (τ : ℝ) {z : Space} (hz : z ∉ Axi.axis) :
    Axi.age R z •
        Axi.Nv R (fun m =>
          (c * (lhP ν m₁ (chartSwap m) * lhP ν m₂ (chartSwap m))) • meridE0) τ z =
      ((c / R ^ (2 * d + 1)) * (z 0 ^ 2 + z 1 ^ 2) ^ d *
        (UnforcedLeray.B0191.profileDeriv ν m₁ (z 2) *
          UnforcedLeray.B0191.profileDeriv ν m₂ (z 2))) • Axi.hor z := by
  rw [age_smul_Nv_meridE0 hR (fun x => c * (lhP ν m₁ x * lhP ν m₂ x)) τ hz,
    lhP_chartSwap_chart hR ν m₁ τ hz,
    lhP_chartSwap_chart hR ν m₂ τ hz]
  congr 1
  have hρ : 0 < Axi.ϱ z := Axi.ϱ_pos hz
  have hρne : Axi.ϱ z ≠ 0 := hρ.ne'
  have hRne : R ≠ 0 := hR.ne'
  have hw : z 0 ^ 2 + z 1 ^ 2 = Axi.ϱ z ^ 2 := (Axi.ϱ_sq z).symm
  have hmul_pow : (Axi.ϱ z / R) ^ (m₁ + 1) * (Axi.ϱ z / R) ^ (m₂ + 1) =
      (Axi.ϱ z / R) ^ (2 * d + 4) := by
    rw [← pow_add, hm]
  have hpow : Axi.ϱ z ^ (2 * d + 4) = (Axi.ϱ z ^ 2) ^ d * (Axi.ϱ z ^ 2) ^ 2 := by ring
  have hRpow : R ^ (2 * d + 4) = R ^ (2 * d + 1) * R ^ 3 := by ring
  have hlhs :
      (Axi.ϱ z / R) ^ (m₁ + 1) * UnforcedLeray.B0191.profileDeriv ν m₁ (z 2) *
        ((Axi.ϱ z / R) ^ (m₂ + 1) * UnforcedLeray.B0191.profileDeriv ν m₂ (z 2)) =
      (Axi.ϱ z / R) ^ (2 * d + 4) *
        (UnforcedLeray.B0191.profileDeriv ν m₁ (z 2) *
          UnforcedLeray.B0191.profileDeriv ν m₂ (z 2)) := by
    rw [← hmul_pow]; ring
  rw [hlhs]
  unfold Axi.age
  rw [hw, div_pow, hpow, hRpow]
  field_simp

/-! ### Part 3: `QConst`, `lhP` profile calculus, finite-order mean expansion, and `Jet.JQ` bounds -/

/-- A scalar profile `g : ProfilePoint → ℝ` is invariant under translation along `eqDir`. -/
def QConst (g : ProfilePoint → ℝ) : Prop :=
  ∀ (x : ProfilePoint) (t : ℝ), g (x + t • eqDir) = g x

theorem eqDir_snd (x : ProfilePoint) (t : ℝ) : (x + t • eqDir).2 = x.2 := by
  simp [eqDir]

theorem QConst.const (c : ℝ) : QConst (fun _ => c) := fun _ _ => rfl

theorem QConst.add {f g : ProfilePoint → ℝ} (hf : QConst f) (hg : QConst g) :
    QConst (fun x => f x + g x) :=
  fun x t => by dsimp; rw [hf x t, hg x t]

theorem QConst.sub {f g : ProfilePoint → ℝ} (hf : QConst f) (hg : QConst g) :
    QConst (fun x => f x - g x) :=
  fun x t => by dsimp; rw [hf x t, hg x t]

theorem QConst.neg {f : ProfilePoint → ℝ} (hf : QConst f) :
    QConst (fun x => -f x) :=
  fun x t => by dsimp; rw [hf x t]

theorem QConst.const_mul (c : ℝ) {f : ProfilePoint → ℝ} (hf : QConst f) :
    QConst (fun x => c * f x) :=
  fun x t => by dsimp; rw [hf x t]

theorem QConst.mul {f g : ProfilePoint → ℝ} (hf : QConst f) (hg : QConst g) :
    QConst (fun x => f x * g x) :=
  fun x t => by dsimp; rw [hf x t, hg x t]

theorem QConst.sum {ι : Type*} (s : Finset ι) {f : ι → ProfilePoint → ℝ}
    (hf : ∀ i ∈ s, QConst (f i)) :
    QConst (fun x => ∑ i ∈ s, f i x) :=
  fun x t => Finset.sum_congr rfl fun i hi => hf i hi x t

theorem fderiv_translate_eq {g : ProfilePoint → ℝ} {a : ProfilePoint}
    (hg : ∀ y, g (y + a) = g y) (x : ProfilePoint) :
    fderiv ℝ g (x + a) = fderiv ℝ g x := by
  by_cases hd : DifferentiableAt ℝ g (x + a)
  · have hid : HasFDerivAt (fun y : ProfilePoint => y + a)
        (ContinuousLinearMap.id ℝ ProfilePoint) x :=
      (hasFDerivAt_id x).add_const a
    have hcomp : HasFDerivAt (g ∘ fun y => y + a) (fderiv ℝ g (x + a)) x := by
      simpa using hd.hasFDerivAt.comp x hid
    have heq : (g ∘ fun y => y + a) = g := funext hg
    rw [heq] at hcomp
    exact hcomp.fderiv.symm
  · have hd' : ¬ DifferentiableAt ℝ g x := by
      intro hdx
      apply hd
      have hid : DifferentiableAt ℝ (fun y : ProfilePoint => y - a) (x + a) :=
        differentiableAt_id.sub_const a
      have hdx' : DifferentiableAt ℝ g ((fun y => y - a) (x + a)) := by
        dsimp
        rwa [add_sub_cancel_right]
      have hcomp : DifferentiableAt ℝ (g ∘ fun y => y - a) (x + a) :=
        hdx'.comp (x + a) hid
      have heq : (g ∘ fun y => y - a) = g := funext fun y => by
        dsimp
        have h := hg (y - a)
        rw [sub_add_cancel] at h
        exact h.symm
      rwa [heq] at hcomp
    rw [fderiv_zero_of_not_differentiableAt hd, fderiv_zero_of_not_differentiableAt hd']

theorem QConst.partialEta {g : ProfilePoint → ℝ} (hg : QConst g) :
    QConst (partialEta g) := by
  intro x t
  unfold UnforcedLeray.B0184.partialEta
  rw [fderiv_translate_eq (fun y => hg y t) x]

theorem QConst.partialAge {g : ProfilePoint → ℝ} (hg : QConst g) :
    QConst (partialAge g) := by
  intro x t
  unfold UnforcedLeray.B0184.partialAge
  rw [fderiv_translate_eq (fun y => hg y t) x]

theorem QConst.ageOperator {g : ProfilePoint → ℝ} (hg : QConst g) :
    QConst (ageOperator g) := by
  intro x t
  unfold UnforcedLeray.B0184.ageOperator
  rw [eqDir_snd x t, hg.partialEta x t, hg.partialAge x t]

theorem QConst.ageShift (r : ℝ) {g : ProfilePoint → ℝ} (hg : QConst g) :
    QConst (ageShift r g) :=
  hg.ageOperator.add (hg.const_mul r)

theorem QConst.streamV1 {g : ProfilePoint → ℝ} (hg : QConst g) :
    QConst (streamV1 g) :=
  hg.partialEta.neg

theorem QConst.ageDefect {g : ProfilePoint → ℝ} (hg : QConst g) :
    QConst (ageDefect g) :=
  hg.sub hg.ageOperator

theorem QConst.coeffB1 (ν : ℝ) {g : ProfilePoint → ℝ} (hg : QConst g) :
    QConst (coeffB₁ ν g) := by
  intro x t
  unfold UnforcedLeray.B0188.coeffB₁
  rw [(hg.streamV1.ageShift 2).ageOperator x t]

theorem QConst.coeffB3 (ν : ℝ) {g : ProfilePoint → ℝ} (hg : QConst g) :
    QConst (coeffB₃ ν g) := by
  intro x t
  unfold UnforcedLeray.B0188.coeffB₃
  rw [((hg.ageDefect.ageShift 1).ageShift 1) x t]

theorem QConst.partialQ_eq_zero {g : ProfilePoint → ℝ} (hg : QConst g) (x : ProfilePoint) :
    partialQ g x = 0 := by
  unfold UnforcedLeray.B0184.partialQ
  by_cases hd : DifferentiableAt ℝ g x
  · exact Jet.B2.remQ_fderiv_zero hd (hg x)
  · rw [fderiv_zero_of_not_differentiableAt hd, zero_apply]

/-- Family-level `eqDir`-invariance. -/
def QConstFam (F : Jet.Fam) : Prop :=
  ∀ ν c (tr : UnforcedLeray.B0140.TrainSol ν c), QConst (F ν c tr)

theorem QConstFam.add {F G : Jet.Fam} (hF : QConstFam F) (hG : QConstFam G) :
    QConstFam (F + G) :=
  fun ν c tr => (hF ν c tr).add (hG ν c tr)

theorem QConstFam.sub {F G : Jet.Fam} (hF : QConstFam F) (hG : QConstFam G) :
    QConstFam (F - G) :=
  fun ν c tr => (hF ν c tr).sub (hG ν c tr)

theorem QConstFam.neg {F : Jet.Fam} (hF : QConstFam F) :
    QConstFam (-F) :=
  fun ν c tr => (hF ν c tr).neg

theorem QConstFam.smul (k : ℝ) {F : Jet.Fam} (hF : QConstFam F) :
    QConstFam (k • F) :=
  fun ν c tr => (hF ν c tr).const_mul k

theorem QConstFam.mul {F G : Jet.Fam} (hF : QConstFam F) (hG : QConstFam G) :
    QConstFam (F * G) :=
  fun ν c tr => (hF ν c tr).mul (hG ν c tr)

theorem QConstFam.famNu {F : Jet.Fam} (hF : QConstFam F) :
    QConstFam (Jet.famNu F) :=
  fun ν c tr => (hF ν c tr).const_mul ν

theorem QConstFam.famEta {F : Jet.Fam} (hF : QConstFam F) :
    QConstFam (Jet.famEta F) :=
  fun ν c tr => (hF ν c tr).partialEta

theorem QConstFam.famK {F : Jet.Fam} (hF : QConstFam F) :
    QConstFam (Jet.famK F) :=
  fun ν c tr => (hF ν c tr).ageOperator

theorem QConstFam.famShift (r : ℝ) {F : Jet.Fam} (hF : QConstFam F) :
    QConstFam (Jet.famShift r F) :=
  fun ν c tr => (hF ν c tr).ageShift r

theorem QConst.lhP (ν : ℝ) (k : ℕ) : QConst (lhP ν k) := by
  intro x t
  show UnforcedLeray.B0191.heatDeriv ν k (x + t • eqDir).2.1 (x + t • eqDir).2.2 =
    UnforcedLeray.B0191.heatDeriv ν k x.2.1 x.2.2
  rw [eqDir_snd x t]

theorem QConstFam.meanFam : QConstFam Jet.meanFam := by
  intro ν c tr x t
  show meanStream tr (x + t • eqDir).2.2 (x + t • eqDir).2.1 =
    meanStream tr x.2.2 x.2.1
  rw [eqDir_snd x t]

theorem QConstFam.v1bar : QConstFam Jet.B2.v1bar :=
  fun ν c tr => (QConstFam.meanFam ν c tr).streamV1

theorem QConstFam.hbar : QConstFam Jet.B2.hbar :=
  fun ν c tr => (QConstFam.meanFam ν c tr).ageDefect

theorem QConstFam.meanB1 : QConstFam meanB1 :=
  fun ν c tr => (QConstFam.meanFam ν c tr).coeffB1 ν

theorem QConstFam.meanB3 : QConstFam meanB3 :=
  fun ν c tr => (QConstFam.meanFam ν c tr).coeffB3 ν

theorem QConstFam.meanA1 : QConstFam meanA1 :=
  (((QConstFam.v1bar.mul QConstFam.v1bar.famK).neg).add
    (QConstFam.hbar.mul QConstFam.v1bar.famEta)).sub
    (QConstFam.v1bar.mul QConstFam.v1bar)

/-! #### `lhP` profile calculus on `ageDomain` -/

theorem lhP_contDiffOn {ν : ℝ} (hν : 0 < ν) (k : ℕ) :
    ContDiffOn ℝ ∞ (lhP ν k) ageDomain :=
  (contDiffOn_partialEta_iter (Jet.heatProfile_contDiffOn_jet hν) k).congr
    (fun y hy => (lhIter ν k y hy).symm)

theorem lhP_ageOperator (ν : ℝ) (k : ℕ) {x : ProfilePoint} (hx : x ∈ ageDomain) :
    ageOperator (lhP ν k) x = -((k : ℝ) + 1) * lhP ν k x := by
  have hx0 : 0 < x.2.2 := hx
  have hxne : x.2.2 ≠ 0 := hx0.ne'
  unfold UnforcedLeray.B0184.ageOperator
  rw [lhPartialEta ν k hx0, lhPartialAge ν k hx0]
  field_simp
  ring

theorem lhP_ageShift (ν r : ℝ) (k : ℕ) {x : ProfilePoint} (hx : x ∈ ageDomain) :
    ageShift r (lhP ν k) x = (r - ((k : ℝ) + 1)) * lhP ν k x := by
  unfold UnforcedLeray.B0188.ageShift
  rw [lhP_ageOperator ν k hx]
  ring

theorem lhP_streamV1 (ν : ℝ) (k : ℕ) {x : ProfilePoint} (hx : x ∈ ageDomain) :
    streamV1 (lhP ν k) x = -lhP ν (k + 1) x := by
  unfold UnforcedLeray.B0185.streamV1
  rw [lhPartialEta ν k hx]

theorem lhP_ageDefect (ν : ℝ) (k : ℕ) {x : ProfilePoint} (hx : x ∈ ageDomain) :
    ageDefect (lhP ν k) x = ((k : ℝ) + 2) * lhP ν k x := by
  unfold UnforcedLeray.B0185.ageDefect
  rw [lhP_ageOperator ν k hx]
  ring

theorem partialEta_congr_nhds {f g : ProfilePoint → ℝ} {x : ProfilePoint} (h : f =ᶠ[𝓝 x] g) :
    partialEta f x = partialEta g x :=
  lhPartialEtaCongr h

theorem partialAge_congr_nhds {f g : ProfilePoint → ℝ} {x : ProfilePoint} (h : f =ᶠ[𝓝 x] g) :
    partialAge f x = partialAge g x :=
  lhPartialAgeCongr h

theorem ageOperator_congr_nhds {f g : ProfilePoint → ℝ} {x : ProfilePoint} (h : f =ᶠ[𝓝 x] g) :
    ageOperator f x = ageOperator g x := by
  unfold UnforcedLeray.B0184.ageOperator
  rw [partialEta_congr_nhds h, partialAge_congr_nhds h]

theorem ageShift_congr_nhds (r : ℝ) {f g : ProfilePoint → ℝ} {x : ProfilePoint} (h : f =ᶠ[𝓝 x] g) :
    ageShift r f x = ageShift r g x := by
  unfold UnforcedLeray.B0188.ageShift
  rw [ageOperator_congr_nhds h, h.eq_of_nhds]

theorem fderiv_const_mul_any (c : ℝ) (f : ProfilePoint → ℝ) (x : ProfilePoint) :
    fderiv ℝ (fun y => c * f y) x = c • fderiv ℝ f x := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [fderiv_const_apply]
  · by_cases hd : DifferentiableAt ℝ f x
    · exact fderiv_const_mul hd c
    · have hd' : ¬ DifferentiableAt ℝ (fun y => c * f y) x := by
        intro hcd
        apply hd
        have h := hcd.const_mul c⁻¹
        have heq : (fun y => c⁻¹ * (c * f y)) = f :=
          funext fun y => inv_mul_cancel_left₀ hc (f y)
        rwa [heq] at h
      rw [fderiv_zero_of_not_differentiableAt hd, fderiv_zero_of_not_differentiableAt hd', smul_zero]

theorem partialEta_const_mul (c : ℝ) (f : ProfilePoint → ℝ) (x : ProfilePoint) :
    partialEta (fun y => c * f y) x = c * partialEta f x := by
  unfold UnforcedLeray.B0184.partialEta
  rw [fderiv_const_mul_any, smul_apply, smul_eq_mul]

theorem partialAge_const_mul (c : ℝ) (f : ProfilePoint → ℝ) (x : ProfilePoint) :
    partialAge (fun y => c * f y) x = c * partialAge f x := by
  unfold UnforcedLeray.B0184.partialAge
  rw [fderiv_const_mul_any, smul_apply, smul_eq_mul]

theorem ageOperator_const_mul (c : ℝ) (f : ProfilePoint → ℝ) (x : ProfilePoint) :
    ageOperator (fun y => c * f y) x = c * ageOperator f x := by
  unfold UnforcedLeray.B0184.ageOperator
  rw [partialEta_const_mul, partialAge_const_mul]
  ring

theorem ageShift_const_mul (r c : ℝ) (f : ProfilePoint → ℝ) (x : ProfilePoint) :
    ageShift r (fun y => c * f y) x = c * ageShift r f x := by
  unfold UnforcedLeray.B0188.ageShift
  rw [ageOperator_const_mul]
  ring

theorem streamV1_const_mul (c : ℝ) (f : ProfilePoint → ℝ) (x : ProfilePoint) :
    streamV1 (fun y => c * f y) x = c * streamV1 f x := by
  unfold UnforcedLeray.B0185.streamV1
  rw [partialEta_const_mul]
  ring

theorem ageDefect_const_mul (c : ℝ) (f : ProfilePoint → ℝ) (x : ProfilePoint) :
    ageDefect (fun y => c * f y) x = c * ageDefect f x := by
  unfold UnforcedLeray.B0185.ageDefect
  rw [ageOperator_const_mul]
  ring

theorem coeffB1_const_mul (ν c : ℝ) (f : ProfilePoint → ℝ) (x : ProfilePoint) :
    coeffB₁ ν (fun y => c * f y) x = c * coeffB₁ ν f x := by
  unfold UnforcedLeray.B0188.coeffB₁
  have h1 : streamV1 (fun y => c * f y) = fun y => c * streamV1 f y :=
    funext (streamV1_const_mul c f)
  have h2 : ageShift 2 (fun y => c * streamV1 f y) = fun y => c * ageShift 2 (streamV1 f) y :=
    funext (ageShift_const_mul 2 c (streamV1 f))
  rw [h1, h2, ageOperator_const_mul]
  ring

theorem coeffB3_const_mul (ν c : ℝ) (f : ProfilePoint → ℝ) (x : ProfilePoint) :
    coeffB₃ ν (fun y => c * f y) x = c * coeffB₃ ν f x := by
  unfold UnforcedLeray.B0188.coeffB₃
  have h1 : ageDefect (fun y => c * f y) = fun y => c * ageDefect f y :=
    funext (ageDefect_const_mul c f)
  have h2 : ageShift 1 (fun y => c * ageDefect f y) = fun y => c * ageShift 1 (ageDefect f) y :=
    funext (ageShift_const_mul 1 c (ageDefect f))
  rw [h1, h2, ageShift_const_mul]
  ring

theorem lhP_coeffB1 (ν : ℝ) (j : ℕ) {x : ProfilePoint} (hx : x ∈ ageDomain) :
    coeffB₁ ν (lhP ν (2 * j)) x =
      ν * (2 * (j : ℝ)) * (2 * (j : ℝ) + 2) * lhP ν (2 * j + 1) x := by
  unfold UnforcedLeray.B0188.coeffB₁
  have h1 : streamV1 (lhP ν (2 * j)) =ᶠ[𝓝 x] fun y => (-1 : ℝ) * lhP ν (2 * j + 1) y := by
    refine Filter.eventuallyEq_of_mem (lhMemNhds hx) fun y hy => ?_
    rw [lhP_streamV1 ν (2 * j) hy]
    ring
  have h2 : ageShift 2 (streamV1 (lhP ν (2 * j))) =ᶠ[𝓝 x]
      fun y => (2 * (j : ℝ)) * lhP ν (2 * j + 1) y := by
    refine Filter.eventuallyEq_of_mem (lhMemNhds hx) fun y hy => ?_
    have h1y : streamV1 (lhP ν (2 * j)) =ᶠ[𝓝 y] fun z => (-1 : ℝ) * lhP ν (2 * j + 1) z := by
      refine Filter.eventuallyEq_of_mem (lhMemNhds hy) fun z hz => ?_
      rw [lhP_streamV1 ν (2 * j) hz]
      ring
    rw [ageShift_congr_nhds 2 h1y, ageShift_const_mul, lhP_ageShift ν 2 (2 * j + 1) hy]
    push_cast
    ring
  rw [ageOperator_congr_nhds h2, ageOperator_const_mul, lhP_ageOperator ν (2 * j + 1) hx]
  push_cast
  ring

theorem lhP_coeffB3 (ν : ℝ) (j : ℕ) {x : ProfilePoint} (hx : x ∈ ageDomain) :
    coeffB₃ ν (lhP ν (2 * j)) x =
      -ν * (2 * (j : ℝ)) ^ 2 * (2 * (j : ℝ) + 2) * lhP ν (2 * j) x := by
  unfold UnforcedLeray.B0188.coeffB₃
  have h1 : ageDefect (lhP ν (2 * j)) =ᶠ[𝓝 x]
      fun y => (2 * (j : ℝ) + 2) * lhP ν (2 * j) y := by
    refine Filter.eventuallyEq_of_mem (lhMemNhds hx) fun y hy => ?_
    rw [lhP_ageDefect ν (2 * j) hy]
    push_cast
    ring
  have h2 : ageShift 1 (ageDefect (lhP ν (2 * j))) =ᶠ[𝓝 x]
      fun y => (-(2 * (j : ℝ)) * (2 * (j : ℝ) + 2)) * lhP ν (2 * j) y := by
    refine Filter.eventuallyEq_of_mem (lhMemNhds hx) fun y hy => ?_
    have h1y : ageDefect (lhP ν (2 * j)) =ᶠ[𝓝 y]
        fun z => (2 * (j : ℝ) + 2) * lhP ν (2 * j) z := by
      refine Filter.eventuallyEq_of_mem (lhMemNhds hy) fun z hz => ?_
      rw [lhP_ageDefect ν (2 * j) hz]
      push_cast
      ring
    rw [ageShift_congr_nhds 1 h1y, ageShift_const_mul, lhP_ageShift ν 1 (2 * j) hy]
    push_cast
    ring
  rw [ageShift_congr_nhds 1 h2, ageShift_const_mul, lhP_ageShift ν 1 (2 * j) hx]
  push_cast
  ring

/-! #### Finite-order mean-stream expansion families and `Jet.JQ` membership -/

/-- The `j`-th term `a_{2j} ∂_η^{2j} G_{νs}` of the mean-stream expansion. -/
def heatTermFam (j : ℕ) : Jet.Fam :=
  fun ν _ tr x => meanCoeff tr j * lhP ν (2 * j) x

/-- The partial sum `∑_{j ≤ M} a_{2j} ∂_η^{2j} G_{νs}` of the mean-stream expansion. -/
def heatSumFam (M : ℕ) : Jet.Fam :=
  fun ν c tr x => ∑ j ∈ Finset.range (M + 1), heatTermFam j ν c tr x

/-- The order-`M` remainder `R_M(η, s)` of the mean-stream expansion. -/
def remFam (M : ℕ) : Jet.Fam :=
  fun _ _ tr => trainProfile fun s z => meanRemainder tr M s z.2

theorem QConstFam.heatTermFam (j : ℕ) : QConstFam (heatTermFam j) :=
  fun ν _ tr => (QConst.lhP ν (2 * j)).const_mul (meanCoeff tr j)

theorem QConstFam.heatSumFam (M : ℕ) : QConstFam (heatSumFam M) :=
  fun ν c tr => QConst.sum (Finset.range (M + 1)) (fun j _ => QConstFam.heatTermFam j ν c tr)

theorem QConstFam.remFam (M : ℕ) : QConstFam (remFam M) := by
  intro _ c tr x t
  show meanRemainder tr M (x + t • eqDir).2.2 (x + t • eqDir).2.1 =
    meanRemainder tr M x.2.2 x.2.1
  rw [eqDir_snd x t]

/-- Pointwise decomposition `S = ∑_{j ≤ M} a_{2j} ∂_η^{2j} G_{νs} + R_M` everywhere on
`ProfilePoint`. -/
theorem meanFam_eq_heatSum_add_rem (M : ℕ) :
    Jet.meanFam = heatSumFam M + remFam M := by
  funext ν c tr x
  change meanStream tr x.2.2 x.2.1 =
    (∑ j ∈ Finset.range (M + 1), meanCoeff tr j * lhP ν (2 * j) x) +
      meanRemainder tr M x.2.2 x.2.1
  have hsum : (∑ j ∈ Finset.range (M + 1), meanCoeff tr j * lhP ν (2 * j) x) =
      ∑ j ∈ Finset.range (M + 1),
        meanCoeff tr j * iteratedDeriv (2 * j) (heatKernel1 (ν * x.2.2)) x.2.1 :=
    Finset.sum_congr rfl fun j _ => by rw [lhP_eq]
  rw [hsum, meanRemainder]
  ring

theorem heatTermFam_smooth (j : ℕ) : Jet.JSmooth (heatTermFam j) :=
  fun _ _ hν _ _ _ => contDiffOn_const.mul (lhP_contDiffOn hν (2 * j))

theorem heatSumFam_smooth (M : ℕ) : Jet.JSmooth (heatSumFam M) := by
  induction M with
  | zero =>
    intro ν c hν hc tr htr
    have heq : heatSumFam 0 ν c tr = heatTermFam 0 ν c tr := by
      funext x
      simp [heatSumFam]
    rw [heq]
    exact heatTermFam_smooth 0 ν c hν hc tr htr
  | succ M ih =>
    intro ν c hν hc tr htr
    have heq : heatSumFam (M + 1) ν c tr =
        fun x => heatSumFam M ν c tr x + heatTermFam (M + 1) ν c tr x := by
      funext x
      simp [heatSumFam, Finset.sum_range_succ]
    rw [heq]
    exact (ih ν c hν hc tr htr).add (heatTermFam_smooth (M + 1) ν c hν hc tr htr)

theorem remFam_smooth (M : ℕ) : Jet.JSmooth (remFam M) := by
  intro ν c hν hc tr htr
  have heq : remFam M ν c tr = fun x => Jet.meanFam ν c tr x - heatSumFam M ν c tr x := by
    funext x
    have h := congr_fun (congr_fun (congr_fun (congr_fun (meanFam_eq_heatSum_add_rem M) ν) c) tr) x
    change meanStream tr x.2.2 x.2.1 =
      heatSumFam M ν c tr x + remFam M ν c tr x at h
    change remFam M ν c tr x = meanStream tr x.2.2 x.2.1 - heatSumFam M ν c tr x
    linarith
  rw [heq]
  exact ((Jet.meanSmoothQ_of lateIngredients).1 ν c hν hc tr htr).sub
    (heatSumFam_smooth M ν c hν hc tr htr)

/-- Weighted late size of the heat word `a_{2j} (-(b + 2j + 1))^ℓ ∂_η^{b + 2j} G_{νs}`. -/
theorem heatTermWord_ww (j ℓ b : ℕ) :
    Jet.WW (((j : ℝ) + 1 / 2) + (b : ℝ) / 2)
      (fun ν _ tr x =>
        meanCoeff tr j *
          ((-(((b + 2 * j : ℕ) : ℝ) + 1)) ^ ℓ * (partialEta^[b + 2 * j] (heatProfile ν)) x)) := by
  intro ρ m hρ
  obtain ⟨Ca, Na, νa, hνa, Ha⟩ := lateIngredients.coeff ρ j hρ
  obtain ⟨Ch, hCh, Hh⟩ := lateIngredients.heat.2.1 m (b + 2 * j)
  set K : ℕ := b + 2 * j
  refine ⟨max Ca 0 * ((K : ℝ) + 1) ^ ℓ * Ch, Na + (K + 1), min νa 1, lt_min hνa one_pos,
    fun ν hν hνle tr htr x hx => ?_⟩
  dsimp only
  have hexp_eq : ((j : ℝ) + 1 / 2) + (b : ℝ) / 2 = ((K : ℝ) + 1) / 2 := by
    dsimp [K]
    push_cast
    ring
  rw [hexp_eq]
  have hν1 : ν ≤ 1 := hνle.trans (min_le_right _ _)
  have hνa' : ν ≤ νa := hνle.trans (min_le_left _ _)
  have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν _
  have hinv : 0 < ν⁻¹ := inv_pos.2 hν
  have hs1 : 1 ≤ x.2.2 := hx
  have hs0 : 0 < x.2.2 := by linarith
  have hA' : |meanCoeff tr j| ≤ polyConst (max Ca 0) Na ν (ν ^ (-ρ)) :=
    (Ha ν hν hνa' tr htr).trans (polyConst_mono hν hc (le_max_left Ca 0) (le_max_right Ca 0) le_rfl)
  have hA0 : 0 ≤ polyConst (max Ca 0) Na ν (ν ^ (-ρ)) := (abs_nonneg _).trans hA'
  have hB : (1 + x.2.1 ^ 2 / x.2.2) ^ m * |(partialEta^[K] (heatProfile ν)) x| ≤
      Ch * (ν * x.2.2) ^ (-(((K : ℝ) + 1) / 2)) :=
    Hh ν hν hν1 x hs1
  have hsplit : (ν * x.2.2) ^ (-(((K : ℝ) + 1) / 2)) =
      ν ^ (-(((K : ℝ) + 1) / 2)) * x.2.2 ^ (-(((K : ℝ) + 1) / 2)) :=
    Real.mul_rpow hν.le hs0.le
  have hi1 : (1 : ℝ) ≤ ν⁻¹ := by nlinarith [mul_inv_cancel₀ hν.ne']
  have hnu : ν ^ (-(((K : ℝ) + 1) / 2)) ≤ (1 + ν ^ (-ρ) + ν⁻¹) ^ (K + 1) := by
    have e1 : ν ^ (-(((K : ℝ) + 1) / 2)) = ν⁻¹ ^ (((K : ℝ) + 1) / 2) := by
      rw [Real.rpow_neg hν.le, Real.inv_rpow hν.le]
    have hb0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
    have e2 : ν⁻¹ ^ (((K : ℝ) + 1) / 2) ≤ ν⁻¹ ^ ((K : ℝ) + 1) :=
      Real.rpow_le_rpow_of_exponent_le hi1 (by linarith)
    have e3 : ν⁻¹ ^ ((K : ℝ) + 1) = ν⁻¹ ^ (K + 1) := by
      rw [← Real.rpow_natCast]; norm_cast
    have e4 : ν⁻¹ ^ (K + 1) ≤ (1 + ν ^ (-ρ) + ν⁻¹) ^ (K + 1) :=
      pow_le_pow_left₀ hinv.le (by linarith) _
    rw [e1]; linarith
  have hP : (0 : ℝ) ≤ ((K : ℝ) + 1) ^ ℓ := by positivity
  have hW : (1 + x.2.1 ^ 2 / x.2.2) ^ m *
      |meanCoeff tr j * ((-((K : ℝ) + 1)) ^ ℓ * (partialEta^[K] (heatProfile ν)) x)| =
      |meanCoeff tr j| * ((K : ℝ) + 1) ^ ℓ *
        ((1 + x.2.1 ^ 2 / x.2.2) ^ m * |(partialEta^[K] (heatProfile ν)) x|) := by
    rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < (K : ℝ) + 1)]
    ring
  have hWB : (1 + x.2.1 ^ 2 / x.2.2) ^ m * |(partialEta^[K] (heatProfile ν)) x| ≤
      Ch * (ν ^ (-(((K : ℝ) + 1) / 2)) * x.2.2 ^ (-(((K : ℝ) + 1) / 2))) := by
    rw [← hsplit]; exact hB
  have hmain : |meanCoeff tr j| * ((K : ℝ) + 1) ^ ℓ *
      ((1 + x.2.1 ^ 2 / x.2.2) ^ m * |(partialEta^[K] (heatProfile ν)) x|) ≤
      polyConst (max Ca 0) Na ν (ν ^ (-ρ)) * ((K : ℝ) + 1) ^ ℓ *
        (Ch * (ν ^ (-(((K : ℝ) + 1) / 2)) * x.2.2 ^ (-(((K : ℝ) + 1) / 2)))) :=
    mul_le_mul (mul_le_mul_of_nonneg_right hA' hP) hWB
      (mul_nonneg (Jet.weight_nonneg m hs1) (abs_nonneg _)) (mul_nonneg hA0 hP)
  have hfin : polyConst (max Ca 0) Na ν (ν ^ (-ρ)) * ((K : ℝ) + 1) ^ ℓ *
      (Ch * (ν ^ (-(((K : ℝ) + 1) / 2)) * x.2.2 ^ (-(((K : ℝ) + 1) / 2)))) ≤
      polyConst (max Ca 0 * ((K : ℝ) + 1) ^ ℓ * Ch) (Na + (K + 1)) ν (ν ^ (-ρ)) *
        x.2.2 ^ (-(((K : ℝ) + 1) / 2)) := by
    have hm : ν ^ (-(((K : ℝ) + 1) / 2)) * x.2.2 ^ (-(((K : ℝ) + 1) / 2)) ≤
        (1 + ν ^ (-ρ) + ν⁻¹) ^ (K + 1) * x.2.2 ^ (-(((K : ℝ) + 1) / 2)) :=
      mul_le_mul_of_nonneg_right hnu (Real.rpow_nonneg hs0.le _)
    have h2 : Ch * (ν ^ (-(((K : ℝ) + 1) / 2)) * x.2.2 ^ (-(((K : ℝ) + 1) / 2))) ≤
        Ch * ((1 + ν ^ (-ρ) + ν⁻¹) ^ (K + 1) * x.2.2 ^ (-(((K : ℝ) + 1) / 2))) :=
      mul_le_mul_of_nonneg_left hm hCh
    calc polyConst (max Ca 0) Na ν (ν ^ (-ρ)) * ((K : ℝ) + 1) ^ ℓ *
          (Ch * (ν ^ (-(((K : ℝ) + 1) / 2)) * x.2.2 ^ (-(((K : ℝ) + 1) / 2))))
        ≤ polyConst (max Ca 0) Na ν (ν ^ (-ρ)) * ((K : ℝ) + 1) ^ ℓ *
          (Ch * ((1 + ν ^ (-ρ) + ν⁻¹) ^ (K + 1) * x.2.2 ^ (-(((K : ℝ) + 1) / 2)))) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hA0 hP)
      _ = polyConst (max Ca 0 * ((K : ℝ) + 1) ^ ℓ * Ch) (Na + (K + 1)) ν (ν ^ (-ρ)) *
          x.2.2 ^ (-(((K : ℝ) + 1) / 2)) := by
          unfold polyConst; ring
  exact hW.trans_le (hmain.trans hfin)

/-- `WordsW ((j : ℝ) + 1 / 2)` for `heatTermFam j`. -/
theorem heatTermFam_words (j : ℕ) : Jet.WordsW ((j : ℝ) + 1 / 2) (heatTermFam j) := by
  have hH := Jet.heatWords_of lateIngredients.heat Jet.jetToolkit.iterLin
  have hL := Jet.jetToolkit.iterLin
  refine ⟨heatTermFam_smooth j, ?_, fun ℓ b => ?_⟩
  · intro ν c _ _ tr _ x _
    exact (QConstFam.heatTermFam j ν c tr).partialQ_eq_zero x
  · have hEq : Jet.LateEq (Jet.wordW ℓ b (heatTermFam j))
        (fun ν _ tr x =>
          meanCoeff tr j *
            ((-(((b + 2 * j : ℕ) : ℝ) + 1)) ^ ℓ *
              (partialEta^[b + 2 * j] (heatProfile ν)) x)) := by
      intro ν c hν _ tr _ x hx
      have heq_on : EqOn (heatTermFam j ν c tr)
          (fun y => meanCoeff tr j * (partialEta^[2 * j] (heatProfile ν)) y)
          {y : ProfilePoint | 0 < y.2.2} := by
        intro y hy
        dsimp [heatTermFam]
        rw [lhIter ν (2 * j) y hy]
      have h1 := hL.1 _ _ heq_on ℓ b 0 hx
      have hG : ContDiffOn ℝ ∞ (partialEta^[2 * j] (heatProfile ν))
          {y : ProfilePoint | 0 < y.2.2} :=
        contDiffOn_partialEta_iter (Jet.heatProfile_contDiffOn_jet hν) (2 * j)
      have h2 := hL.2.2 (partialEta^[2 * j] (heatProfile ν)) hG (meanCoeff tr j) ℓ b 0 hx
      simp only [Function.iterate_zero, id_eq] at h1 h2
      have h3 : (ageOperator^[ℓ] (partialEta^[b] (partialEta^[2 * j] (heatProfile ν)))) x =
          (ageOperator^[ℓ] (partialEta^[b + 2 * j] (heatProfile ν))) x := by
        rw [Function.iterate_add_apply]
      have h4 := (hH ν hν).2 ℓ (b + 2 * j) hx
      change (ageOperator^[ℓ] (partialEta^[b] (heatTermFam j ν c tr))) x = _
      rw [h1, h2, h3, h4]
    exact Jet.WW.congr hEq.symm (heatTermWord_ww j ℓ b)

theorem heatTermFam_jq (j n : ℕ) : Jet.JQ n ((j : ℝ) + 1 / 2) (heatTermFam j) :=
  Jet.JQ_of_words Jet.jetToolkit.jc Jet.jetToolkit.wordW n _ _ (heatTermFam_words j)

theorem heatSumFam_jq (M n : ℕ) : Jet.JQ n (1 / 2) (heatSumFam M) := by
  have hT := Jet.jetToolkit
  induction M with
  | zero =>
    have heq : heatSumFam 0 = heatTermFam 0 := by
      funext ν c tr x
      simp [heatSumFam]
    rw [heq]
    exact hT.jc.qmono (by norm_num) (heatTermFam_jq 0 n)
  | succ M ih =>
    have heq : heatSumFam (M + 1) = heatSumFam M + heatTermFam (M + 1) := by
      funext ν c tr x
      simp [heatSumFam, Finset.sum_range_succ]
    rw [heq]
    exact hT.jc.qadd ih
      (hT.jc.qmono (by linarith [Nat.cast_nonneg (α := ℝ) (M + 1)]) (heatTermFam_jq (M + 1) n))

/-- `WordsW ((M : ℝ) + 3 / 2)` for the order-`M` remainder `remFam M`. -/
theorem remFam_words (M : ℕ) : Jet.WordsW ((M : ℝ) + 3 / 2) (remFam M) := by
  refine ⟨remFam_smooth M, ?_, fun ℓ b => ?_⟩
  · intro ν c _ _ tr _ x _
    exact (QConstFam.remFam M ν c tr).partialQ_eq_zero x
  · intro ρ m hρ
    obtain ⟨C, d, ν₀, hν₀, H⟩ := lateIngredients.remainder ρ M m b ℓ hρ
    refine ⟨C, d, ν₀, hν₀, fun ν hν hle tr htr x hx => ?_⟩
    have hb := H ν hν hle tr htr x hx
    have e : -(((M : ℝ) + 3 / 2) + (b : ℝ) / 2) = -(((b : ℝ) + 2 * (M : ℝ) + 3) / 2) := by
      ring
    show (1 + x.2.1 ^ 2 / x.2.2) ^ m *
        |(ageOperator^[ℓ] (partialEta^[b] (trainProfile fun s z => meanRemainder tr M s z.2))) x| ≤
      polyConst C d ν (ν ^ (-ρ)) * x.2.2 ^ (-(((M : ℝ) + 3 / 2) + (b : ℝ) / 2))
    rw [e]
    exact hb

theorem remFam_jq (M n : ℕ) : Jet.JQ n ((M : ℝ) + 3 / 2) (remFam M) :=
  Jet.JQ_of_words Jet.jetToolkit.jc Jet.jetToolkit.wordW n _ _ (remFam_words M)

/-! #### From `Jet.JQ` membership and `QConstFam` to the remainder directional-partial bound -/

theorem jq_famEta_iter : ∀ (j n : ℕ) {a : ℝ} {F : Jet.Fam},
    Jet.JQ (n + j) a F →
    Jet.JQ n (a + (j : ℝ) / 2) (fun ν c tr => partialEta^[j] (F ν c tr))
  | 0, n, a, F, h => by
    simpa using h
  | j + 1, n, a, F, h => by
    have h' : Jet.JQ ((n + 1) + j) a F := by rw [Nat.add_right_comm]; exact h
    have ih := (jq_famEta_iter j (n + 1) h').eta
    have heq : Jet.famEta (fun ν c tr => partialEta^[j] (F ν c tr)) =
        fun ν c tr => partialEta^[j + 1] (F ν c tr) := by
      funext ν c tr
      exact (Function.iterate_succ_apply' partialEta j (F ν c tr)).symm
    have hexp : a + (j : ℝ) / 2 + 1 / 2 = a + ((j + 1 : ℕ) : ℝ) / 2 := by
      push_cast; ring
    rw [heq, hexp] at ih
    exact ih

theorem jq_famK_iter : ∀ (k n : ℕ) {a : ℝ} {F : Jet.Fam},
    Jet.JQ (n + k) a F →
    Jet.JQ n a (fun ν c tr => ageOperator^[k] (F ν c tr))
  | 0, n, _, _, h => by
    simpa using h
  | k + 1, n, a, F, h => by
    have h' : Jet.JQ ((n + 1) + k) a F := by rw [Nat.add_right_comm]; exact h
    have ih := (jq_famK_iter k (n + 1) h').k
    have heq : Jet.famK (fun ν c tr => ageOperator^[k] (F ν c tr)) =
        fun ν c tr => ageOperator^[k + 1] (F ν c tr) := by
      funext ν c tr
      exact (Function.iterate_succ_apply' ageOperator k (F ν c tr)).symm
    rwa [heq] at ih

theorem jq_word_zero {a : ℝ} {F : Jet.Fam} (hF : ∀ n, Jet.JQ n a F) (k j : ℕ) :
    Jet.JQ 0 a (fun ν c tr => ageOperator^[k] (partialEta^[j] (F ν c tr))) :=
  Jet.jetToolkit.jc.qmono (by linarith [Nat.cast_nonneg (α := ℝ) j] : a ≤ a + (j : ℝ) / 2)
    (jq_famK_iter k 0 (jq_famEta_iter j (0 + k) (hF (0 + k + j))))

theorem jq_zero_wtd_bound {a : ℝ} {G : Jet.Fam} (hG : Jet.JQ 0 a G) (m : ℕ) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ p : Params, IsBUCTrain p.train → p.ν < ν₀ →
      p.c = (p.ν ^ 2)⁻¹ →
        ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ProfilePoint, 1 ≤ x.2.2 →
          (1 + x.2.1 ^ 2 / x.2.2) ^ m * |G p.ν p.c p.train x| ≤ B * x.2.2 ^ (-a) := by
  obtain ⟨C₀, d₀, ν₀, hν₀, H⟩ := hG.ww 2 m (by norm_num)
  refine ⟨ν₀, hν₀, fun p htr hν hc => ?_⟩
  have hc_rpow : p.c = p.ν ^ (-(2 : ℝ)) := by
    rw [hc, show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg p.ν_pos.le, Real.rpow_natCast]
  have hWtd_gen : ∀ (c : ℝ) (tr : UnforcedLeray.B0140.TrainSol p.ν c),
      c = p.ν ^ (-(2 : ℝ)) → IsBUCTrain tr →
      WtdBound m (G p.ν c tr) a (polyConst C₀ d₀ p.ν c) := by
    rintro _ tr rfl htr'
    exact H p.ν p.ν_pos hν.le tr htr'
  have hWtd : WtdBound m (G p.ν p.c p.train) a (polyConst C₀ d₀ p.ν p.c) :=
    hWtd_gen p.c p.train hc_rpow htr
  set P₀ : ℝ := max (polyConst C₀ d₀ p.ν p.c) 0
  refine ⟨P₀, le_max_right _ _, fun x hx1 => ?_⟩
  have hs0 : 0 < x.2.2 := lt_of_lt_of_le one_pos hx1
  exact (hWtd x hx1).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hs0.le _))

/-- For any `q`-independent family `F` with `∀ n, Jet.JQ n (N : ℝ) F`, there is a viscosity
threshold `ν₀ > 0` such that for `p.ν < ν₀`, `p.c = (p.ν ^ 2)⁻¹`, `2 ≤ p.R`, and any `r : ℕ`,
`fun x => ringEps p.R ^ r * F p.ν p.c p.train x` is `C^∞` on `ageDomain` and satisfies the
weighted directional-partial bound of `ScalarMeridLateHeatSplit2` at order `N`. -/
theorem jq_late_partials_bound {N : ℕ} {F : Jet.Fam}
    (hq : QConstFam F) (hF : ∀ n, Jet.JQ n (N : ℝ) F) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ p : Params, IsBUCTrain p.train → p.ν < ν₀ →
      p.c = (p.ν ^ 2)⁻¹ → 2 ≤ p.R → ∀ r : ℕ,
        ContDiffOn ℝ ∞ (fun x => ringEps p.R ^ r * F p.ν p.c p.train x) ageDomain ∧
        ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ProfilePoint, 1 ≤ x.2.2 → ∀ ℓ ≤ 2, ∀ a ≤ 2, ∀ b ≤ 2,
          (1 + x.2.1 ^ 2 / x.2.2) ^ 2 *
            |(partialAge^[ℓ] (partialEta^[a] (partialQ^[b]
              (fun y => ringEps p.R ^ r * F p.ν p.c p.train y)))) x| ≤
              B * x.2.2 ^ (-(N : ℝ)) := by
  choose ν_f hν_f H_f using fun q : Fin 5 × Fin 3 × Fin 5 =>
    jq_zero_wtd_bound (jq_word_zero hF q.2.1.val q.2.2.val) q.1.val
  obtain ⟨ν₀, hν₀, hle⟩ : ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ q : Fin 5 × Fin 3 × Fin 5, ν₀ ≤ ν_f q := by
    refine ⟨Finset.univ.inf' Finset.univ_nonempty ν_f, ?_, fun q =>
      Finset.inf'_le ν_f (Finset.mem_univ q)⟩
    rw [Finset.lt_inf'_iff]
    intro q _
    exact hν_f q
  refine ⟨ν₀, hν₀, fun p htr hν hc hR r => ?_⟩
  have hsm0 : ContDiffOn ℝ ∞ (F p.ν p.c p.train) ageDomain :=
    (hF 0).smooth p.ν p.c p.ν_pos p.c_pos p.train htr
  set f_rem : ProfilePoint → ℝ := fun x => ringEps p.R ^ r * F p.ν p.c p.train x
  have hsm : ContDiffOn ℝ ∞ f_rem ageDomain := contDiffOn_const.mul hsm0
  refine ⟨hsm, ?_⟩
  choose B_f hB0 hB using fun q : Fin 5 × Fin 3 × Fin 5 =>
    H_f q p htr (lt_of_lt_of_le hν (hle q)) hc
  set Bsum : ℝ := ∑ q : Fin 5 × Fin 3 × Fin 5, B_f q
  have hBsum0 : 0 ≤ Bsum := Finset.sum_nonneg fun q _ => hB0 q
  have hR0 : 0 < p.R := by linarith
  have heps0 : 0 ≤ ringEps p.R ^ r := by
    unfold ringEps
    positivity
  refine ⟨9 * (ringEps p.R ^ r * Bsum), mul_nonneg (by norm_num) (mul_nonneg heps0 hBsum0),
    fun x hx1 => ?_⟩
  have hx0 : 0 < x.2.2 := lt_of_lt_of_le one_pos hx1
  have hq_rem : ∀ y ∈ ageDomain, partialQ f_rem y = 0 :=
    fun y _ => ((hq p.ν p.c p.train).const_mul (ringEps p.R ^ r)).partialQ_eq_zero y
  have hK : ∀ m ≤ 4, ∀ k ≤ 2, ∀ j ≤ 4,
      (1 + x.2.1 ^ 2 / x.2.2) ^ m * |(ageOperator^[k] (partialEta^[j] f_rem)) x| ≤
        (ringEps p.R ^ r * Bsum) * x.2.2 ^ (-(N : ℝ)) := by
    intro m hm k hk j hj
    let q : Fin 5 × Fin 3 × Fin 5 := (⟨m, by omega⟩, ⟨k, by omega⟩, ⟨j, by omega⟩)
    have hq_le : B_f q ≤ Bsum :=
      Finset.single_le_sum (fun i _ => hB0 i) (Finset.mem_univ q)
    have hlin := Jet.jetToolkit.iterLin.2.2 (F p.ν p.c p.train) hsm0 (ringEps p.R ^ r) k j 0 hx0
    simp only [Function.iterate_zero, id_eq] at hlin
    have hlin' : (ageOperator^[k] (partialEta^[j] f_rem)) x =
        ringEps p.R ^ r * (ageOperator^[k] (partialEta^[j] (F p.ν p.c p.train))) x := hlin
    rw [hlin', abs_mul, abs_of_nonneg heps0]
    calc (1 + x.2.1 ^ 2 / x.2.2) ^ m *
          (ringEps p.R ^ r * |(ageOperator^[k] (partialEta^[j] (F p.ν p.c p.train))) x|)
        = ringEps p.R ^ r *
            ((1 + x.2.1 ^ 2 / x.2.2) ^ m *
              |(ageOperator^[k] (partialEta^[j] (F p.ν p.c p.train))) x|) := by ring
      _ ≤ ringEps p.R ^ r * (B_f q * x.2.2 ^ (-(N : ℝ))) :=
          mul_le_mul_of_nonneg_left (hB q x hx1) heps0
      _ ≤ ringEps p.R ^ r * (Bsum * x.2.2 ^ (-(N : ℝ))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hq_le (Real.rpow_nonneg hx0.le _)) heps0
      _ = (ringEps p.R ^ r * Bsum) * x.2.2 ^ (-(N : ℝ)) := by ring
  have hBN0 : 0 ≤ (ringEps p.R ^ r * Bsum) * x.2.2 ^ (-(N : ℝ)) :=
    mul_nonneg (mul_nonneg heps0 hBsum0) (Real.rpow_nonneg hx0.le _)
  have hpart := wtd_partials_of_K_eta_jets hsm hq_rem hx1 hBN0 hK
  intro ℓ hℓ a ha b hb
  linarith [hpart ℓ hℓ a ha b hb]

/-- Fixed-order (`N : ℕ` outside `∃ ν₀ : ℝ`) version of `ScalarMeridLateHeatSplit2`. -/
def ScalarMeridLateHeatSplit2At (M : Params → ProfilePoint → ℝ) (v : Axi.Merid) (N : ℕ) : Prop :=
  ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ p : Params, IsBUCTrain p.train → p.ν < ν₀ →
    p.c = (p.ν ^ 2)⁻¹ → 2 ≤ p.R → p.period ≤ 1 →
      ∃ (F_heat : UnforcedLeray.Space → UnforcedLeray.Space)
        (f_rem : ProfilePoint → ℝ) (C_heat B : ℝ),
        0 ≤ B ∧
        ContDiff ℝ ∞ F_heat ∧
        ContDiffOn ℝ ∞ f_rem ageDomain ∧
        (∀ (τ : ℝ) (z : UnforcedLeray.Space), z ∉ Axi.axis →
          Axi.age p.R z • Axi.Nv p.R (fun m => M p (chartSwap m) • v) τ z =
            F_heat z + Axi.age p.R z • Axi.Nv p.R (fun m => f_rem (chartSwap m) • v) τ z) ∧
        (∀ y : UnforcedLeray.Space, Axi.ϱ y ≤ p.R →
          (1 + y 2 ^ 2) * ‖iteratedFDeriv ℝ 2 F_heat y‖ ≤ C_heat) ∧
        (∀ x : ProfilePoint, 1 ≤ x.2.2 → ∀ ℓ ≤ 2, ∀ a ≤ 2, ∀ b ≤ 2,
          (1 + x.2.1 ^ 2 / x.2.2) ^ 2 *
            |(partialAge^[ℓ] (partialEta^[a] (partialQ^[b] f_rem))) x| ≤ B * x.2.2 ^ (-(N : ℝ)))

/-- Uniform-in-`N` version of the `jq_late_partials_bound` conclusion for a family sequence
`F : ℕ → Jet.Fam`. -/
def JQUnif (F : ℕ → Jet.Fam) : Prop :=
  ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ p : Params, IsBUCTrain p.train → p.ν < ν₀ →
    p.c = (p.ν ^ 2)⁻¹ → 2 ≤ p.R → ∀ (r N : ℕ),
      ContDiffOn ℝ ∞ (fun x => ringEps p.R ^ r * F N p.ν p.c p.train x) ageDomain ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ProfilePoint, 1 ≤ x.2.2 → ∀ ℓ ≤ 2, ∀ a ≤ 2, ∀ b ≤ 2,
        (1 + x.2.1 ^ 2 / x.2.2) ^ 2 *
          |(partialAge^[ℓ] (partialEta^[a] (partialQ^[b]
            (fun y => ringEps p.R ^ r * F N p.ν p.c p.train y)))) x| ≤
            B * x.2.2 ^ (-(N : ℝ))

/-! #### Family-level linearity of `streamV1`, `ageDefect`, `coeffB₁`, `coeffB₃` -/

theorem v1_smooth {F : Jet.Fam} (hF : Jet.JSmooth F) : Jet.JSmooth (-Jet.famEta F) := by
  rw [Jet.neg_eq_smul]
  exact (Jet.jetToolkit.smooth (Jet.famEta F) (Jet.famEta F)
    (Jet.jetToolkit.smooth F F hF hF).2.2.2.2.2.1
    (Jet.jetToolkit.smooth F F hF hF).2.2.2.2.2.1).2.2.1 (-1)

theorem defect_smooth {F : Jet.Fam} (hF : Jet.JSmooth F) : Jet.JSmooth (F - Jet.famK F) := by
  rw [Jet.sub_eq_add_neg', Jet.neg_eq_smul]
  have hK := (Jet.jetToolkit.smooth F F hF hF).2.2.2.2.1
  have hnK := (Jet.jetToolkit.smooth (Jet.famK F) (Jet.famK F) hK hK).2.2.1 (-1)
  exact (Jet.jetToolkit.smooth F _ hF hnK).1

theorem shift_smooth (r : ℝ) {F : Jet.Fam} (hF : Jet.JSmooth F) : Jet.JSmooth (Jet.famShift r F) := by
  rw [Jet.famShift_eq]
  have hK := (Jet.jetToolkit.smooth F F hF hF).2.2.2.2.1
  have hrF := (Jet.jetToolkit.smooth F F hF hF).2.2.1 r
  exact (Jet.jetToolkit.smooth _ _ hK hrF).1

theorem v1_add_late {F G : Jet.Fam} (hF : Jet.JSmooth F) (hG : Jet.JSmooth G) :
    Jet.LateEq (-Jet.famEta (F + G)) (-Jet.famEta F + -Jet.famEta G) := by
  have heta := (Jet.jetToolkit.linOps F G hF hG 0).2.1
  intro ν c hν hc tr htr x hx
  have e := heta ν c hν hc tr htr hx
  show -partialEta ((F + G) ν c tr) x = -partialEta (F ν c tr) x + -partialEta (G ν c tr) x
  have e' : partialEta ((F + G) ν c tr) x = partialEta (F ν c tr) x + partialEta (G ν c tr) x := e
  linarith

theorem defect_add_late {F G : Jet.Fam} (hF : Jet.JSmooth F) (hG : Jet.JSmooth G) :
    Jet.LateEq ((F + G) - Jet.famK (F + G)) ((F - Jet.famK F) + (G - Jet.famK G)) := by
  have hk := (Jet.jetToolkit.linOps F G hF hG 0).1
  intro ν c hν hc tr htr x hx
  have e := hk ν c hν hc tr htr hx
  show (F ν c tr x + G ν c tr x) - ageOperator ((F + G) ν c tr) x =
    (F ν c tr x - ageOperator (F ν c tr) x) + (G ν c tr x - ageOperator (G ν c tr) x)
  have e' : ageOperator ((F + G) ν c tr) x = ageOperator (F ν c tr) x + ageOperator (G ν c tr) x := e
  linarith

theorem coeffB1_add_late {F G : Jet.Fam} (hF : Jet.JSmooth F) (hG : Jet.JSmooth G) :
    Jet.LateEq (fun ν c tr => coeffB₁ ν ((F + G) ν c tr))
      ((fun ν c tr => coeffB₁ ν (F ν c tr)) + (fun ν c tr => coeffB₁ ν (G ν c tr))) := by
  have hT := Jet.jetToolkit
  have hv1 := v1_add_late hF hG
  have hs1 := (Jet.B2.shift_congr hT hv1 2).trans
    (Jet.B2.shift_add hT (v1_smooth hF) (v1_smooth hG) 2)
  have hs2 := (hT.eqOps _ _ hs1).1.trans
    (hT.linOps _ _ (shift_smooth 2 (v1_smooth hF)) (shift_smooth 2 (v1_smooth hG)) 0).1
  intro ν c hν hc tr htr x hx
  have e : ageOperator (ageShift 2 (streamV1 ((F + G) ν c tr))) x =
      ageOperator (ageShift 2 (streamV1 (F ν c tr))) x +
        ageOperator (ageShift 2 (streamV1 (G ν c tr))) x :=
    hs2 ν c hν hc tr htr hx
  show coeffB₁ ν ((F + G) ν c tr) x = coeffB₁ ν (F ν c tr) x + coeffB₁ ν (G ν c tr) x
  unfold UnforcedLeray.B0188.coeffB₁
  linear_combination -ν * e

theorem coeffB3_add_late {F G : Jet.Fam} (hF : Jet.JSmooth F) (hG : Jet.JSmooth G) :
    Jet.LateEq (fun ν c tr => coeffB₃ ν ((F + G) ν c tr))
      ((fun ν c tr => coeffB₃ ν (F ν c tr)) + (fun ν c tr => coeffB₃ ν (G ν c tr))) := by
  have hT := Jet.jetToolkit
  have hd := defect_add_late hF hG
  have hs1 := (Jet.B2.shift_congr hT hd 1).trans
    (Jet.B2.shift_add hT (defect_smooth hF) (defect_smooth hG) 1)
  have hs2 := (Jet.B2.shift_congr hT hs1 1).trans
    (Jet.B2.shift_add hT (shift_smooth 1 (defect_smooth hF)) (shift_smooth 1 (defect_smooth hG)) 1)
  intro ν c hν hc tr htr x hx
  have e : ageShift 1 (ageShift 1 (ageDefect ((F + G) ν c tr))) x =
      ageShift 1 (ageShift 1 (ageDefect (F ν c tr))) x +
        ageShift 1 (ageShift 1 (ageDefect (G ν c tr))) x :=
    hs2 ν c hν hc tr htr hx
  show coeffB₃ ν ((F + G) ν c tr) x = coeffB₃ ν (F ν c tr) x + coeffB₃ ν (G ν c tr) x
  unfold UnforcedLeray.B0188.coeffB₃
  linear_combination -ν * e

theorem coeffB1_heatSumFam (M : ℕ) :
    Jet.LateEq (fun ν c tr => coeffB₁ ν (heatSumFam M ν c tr))
      (fun ν _ tr x =>
        ∑ d ∈ Finset.range M,
          (meanCoeff tr (d + 1) *
            (ν * (2 * ((d + 1 : ℕ) : ℝ)) * (2 * ((d + 1 : ℕ) : ℝ) + 2))) *
            lhP ν (2 * d + 3) x) := by
  induction M with
  | zero =>
    intro ν c _ _ tr _ x hx
    have heq : heatSumFam 0 ν c tr = fun y => meanCoeff tr 0 * lhP ν 0 y := by
      funext y
      simp [heatSumFam, heatTermFam]
    change coeffB₁ ν (heatSumFam 0 ν c tr) x = 0
    rw [heq, coeffB1_const_mul, lhP_coeffB1 ν 0 hx]
    simp
  | succ M ih =>
    have hsplit : heatSumFam (M + 1) = heatSumFam M + heatTermFam (M + 1) := by
      funext ν c tr y
      simp [heatSumFam, Finset.sum_range_succ]
    have hadd := coeffB1_add_late (heatSumFam_smooth M) (heatTermFam_smooth (M + 1))
    intro ν c hν hc tr htr x hx
    have e1 : coeffB₁ ν (heatSumFam (M + 1) ν c tr) x =
        coeffB₁ ν (heatSumFam M ν c tr) x + coeffB₁ ν (heatTermFam (M + 1) ν c tr) x := by
      rw [hsplit]
      exact hadd ν c hν hc tr htr hx
    have e2 := ih ν c hν hc tr htr hx
    dsimp only at e2
    have e3 : coeffB₁ ν (heatTermFam (M + 1) ν c tr) x =
        (meanCoeff tr (M + 1) *
          (ν * (2 * ((M + 1 : ℕ) : ℝ)) * (2 * ((M + 1 : ℕ) : ℝ) + 2))) *
          lhP ν (2 * M + 3) x := by
      unfold heatTermFam
      rw [coeffB1_const_mul, lhP_coeffB1 ν (M + 1) hx,
        show 2 * (M + 1) + 1 = 2 * M + 3 by omega]
      ring
    change coeffB₁ ν (heatSumFam (M + 1) ν c tr) x =
      ∑ d ∈ Finset.range (M + 1),
        (meanCoeff tr (d + 1) *
          (ν * (2 * ((d + 1 : ℕ) : ℝ)) * (2 * ((d + 1 : ℕ) : ℝ) + 2))) *
          lhP ν (2 * d + 3) x
    rw [e1, e2, e3, Finset.sum_range_succ]

theorem coeffB3_heatSumFam (M : ℕ) :
    Jet.LateEq (fun ν c tr => coeffB₃ ν (heatSumFam M ν c tr))
      (fun ν _ tr x =>
        ∑ d ∈ Finset.range M,
          (-(meanCoeff tr (d + 1) *
            ν * (2 * ((d + 1 : ℕ) : ℝ)) ^ 2 * (2 * ((d + 1 : ℕ) : ℝ) + 2))) *
            lhP ν (2 * d + 2) x) := by
  induction M with
  | zero =>
    intro ν c _ _ tr _ x hx
    have heq : heatSumFam 0 ν c tr = fun y => meanCoeff tr 0 * lhP ν 0 y := by
      funext y
      simp [heatSumFam, heatTermFam]
    change coeffB₃ ν (heatSumFam 0 ν c tr) x = 0
    rw [heq, coeffB3_const_mul, lhP_coeffB3 ν 0 hx]
    simp
  | succ M ih =>
    have hsplit : heatSumFam (M + 1) = heatSumFam M + heatTermFam (M + 1) := by
      funext ν c tr y
      simp [heatSumFam, Finset.sum_range_succ]
    have hadd := coeffB3_add_late (heatSumFam_smooth M) (heatTermFam_smooth (M + 1))
    intro ν c hν hc tr htr x hx
    have e1 : coeffB₃ ν (heatSumFam (M + 1) ν c tr) x =
        coeffB₃ ν (heatSumFam M ν c tr) x + coeffB₃ ν (heatTermFam (M + 1) ν c tr) x := by
      rw [hsplit]
      exact hadd ν c hν hc tr htr hx
    have e2 := ih ν c hν hc tr htr hx
    dsimp only at e2
    have e3 : coeffB₃ ν (heatTermFam (M + 1) ν c tr) x =
        (-(meanCoeff tr (M + 1) *
          ν * (2 * ((M + 1 : ℕ) : ℝ)) ^ 2 * (2 * ((M + 1 : ℕ) : ℝ) + 2))) *
          lhP ν (2 * M + 2) x := by
      unfold heatTermFam
      rw [coeffB3_const_mul, lhP_coeffB3 ν (M + 1) hx,
        show 2 * (M + 1) = 2 * M + 2 by omega]
      ring
    change coeffB₃ ν (heatSumFam (M + 1) ν c tr) x =
      ∑ d ∈ Finset.range (M + 1),
        (-(meanCoeff tr (d + 1) *
          ν * (2 * ((d + 1 : ℕ) : ℝ)) ^ 2 * (2 * ((d + 1 : ℕ) : ℝ) + 2))) *
          lhP ν (2 * d + 2) x
    rw [e1, e2, e3, Finset.sum_range_succ]

end LateHeatDecomp2Sub
end UnforcedLeray.Short.PartIIIb.Concrete
