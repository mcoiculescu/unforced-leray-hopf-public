import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_1_2_1_2.BlockB1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_1_2_1_2.BlockB3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_1_2_1_2.BlockA1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_1_2_1_2.BlockB2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Sub.RingLiftOffAxis_Sub.RingLiftPtJet
import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.IteratedDiffEq.RawResidualIteratedEnvelope.Calc

/-!
# All-order heat-lift and off-axis `age • Nv` jet bounds for `RawResidualIteratedLateTail`

Source of record: `the November 2 reference manuscript`, lines 1243-1285,
1310-1325, 1656-1680, 2548-2551.

Generalizes the `(1 + y 2 ^ 2)`-weighted Cartesian heat-field jet bounds (`heatB1Field`,
`heatB3Field`, `heatA1Field`, `F_heat_B2`) and the off-axis `Axi.age R • Axi.Nv R b τ` pointwise
jet bound from order `2` to every spatial derivative order `m : ℕ`.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.PhaseSpace MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal BigOperators
open UnforcedLeray.Cons.C03.Concrete (Params)
open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0187 UnforcedLeray.B0188
  UnforcedLeray.B0190 UnforcedLeray.Short.PartIIa
open UnforcedLeray.Short.PartI
open UnforcedLeray.Short.PartIIIb.Concrete
open UnforcedLeray.Short.PartIIIb.Concrete.FarDecaySub
open UnforcedLeray.Short.PartIIIb.Concrete.LateHeatDecomp2Sub

namespace UnforcedLeray.Short.IIb.RawResidualIteratedLateTailAux

/-! ### 1. All-order `(1 + y 2 ^ 2)`-weighted Cartesian heat-field jet bounds -/

/-- Global `C^∞` regularity and `(1 + y 2 ^ 2)`-weighted order-`m` Fréchet derivative bound on
the cylinder `Axi.ϱ y ≤ R`. -/
def WtdHeatJetBdd (m : ℕ) (R : ℝ) (F : Space → Space) : Prop :=
  ContDiff ℝ ∞ F ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Space, Axi.ϱ y ≤ R →
    (1 + y 2 ^ 2) * ‖iteratedFDeriv ℝ m F y‖ ≤ C

theorem wtdHeatJetBdd_zero (m : ℕ) (R : ℝ) : WtdHeatJetBdd m R (fun _ => 0) := by
  refine ⟨contDiff_const, 0, le_rfl, fun y _ => ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [norm_iteratedFDeriv_zero, norm_zero, mul_zero]
  · rw [iteratedFDeriv_const_of_ne hm.ne' (0 : Space)]; simp

theorem wtdHeatJetBdd_add {m : ℕ} {R : ℝ} {F₁ F₂ : Space → Space}
    (h₁ : WtdHeatJetBdd m R F₁) (h₂ : WtdHeatJetBdd m R F₂) :
    WtdHeatJetBdd m R (fun y => F₁ y + F₂ y) := by
  obtain ⟨c₁, C₁, hC₁0, hB₁⟩ := h₁
  obtain ⟨c₂, C₂, hC₂0, hB₂⟩ := h₂
  refine ⟨c₁.add c₂, C₁ + C₂, add_nonneg hC₁0 hC₂0, fun y hy => ?_⟩
  have hadd : iteratedFDeriv ℝ m (fun z => F₁ z + F₂ z) y =
      iteratedFDeriv ℝ m F₁ y + iteratedFDeriv ℝ m F₂ y :=
    iteratedFDeriv_add_apply (c₁.contDiffAt.of_le (by exact_mod_cast le_top))
      (c₂.contDiffAt.of_le (by exact_mod_cast le_top))
  have hw0 : 0 ≤ 1 + y 2 ^ 2 := by positivity
  have hnorm : ‖iteratedFDeriv ℝ m (fun z => F₁ z + F₂ z) y‖ ≤
      ‖iteratedFDeriv ℝ m F₁ y‖ + ‖iteratedFDeriv ℝ m F₂ y‖ := by
    rw [hadd]; exact norm_add_le _ _
  have hmul := mul_le_mul_of_nonneg_left hnorm hw0
  linarith [hB₁ y hy, hB₂ y hy]

theorem wtdHeatJetBdd_sum {m : ℕ} {R : ℝ} {ι : Type*} [DecidableEq ι] (s : Finset ι)
    {F : ι → Space → Space} (h : ∀ i ∈ s, WtdHeatJetBdd m R (F i)) :
    WtdHeatJetBdd m R (fun y => ∑ i ∈ s, F i y) := by
  induction s using Finset.induction_on with
  | empty =>
    simpa using wtdHeatJetBdd_zero m R
  | @insert a s ha ih =>
    have heq : (fun y : Space => ∑ i ∈ insert a s, F i y) =
        fun y => F a y + ∑ i ∈ s, F i y := by
      funext y
      exact Finset.sum_insert ha
    rw [heq]
    exact wtdHeatJetBdd_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Weighted order-`m` jet bound for a separable product `(a y * P (y 2)) • v`. -/
theorem wtdHeatJetBdd_smul_const (m : ℕ) {R : ℝ} (_hR : 0 ≤ R) {a : Space → ℝ}
    (ha : ContDiff ℝ ∞ a) (Ha : HeatJetBdd (R ^ 2) a) {P : ℝ → ℝ} (hP : WtdLineJetBdd P)
    (v : Space) :
    WtdHeatJetBdd m R (fun y : Space => (a y * P (y 2)) • v) := by
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
    ∑ i ∈ Finset.range (m + 1), (Nat.choose m i : ℝ) * Ca i * (CP (m - i) * ‖π₂‖ ^ (m - i))
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
    have hcomp := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv ℝ j P (π₂ y)) (fun _ => π₂)
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hcomp
    calc (1 + y 2 ^ 2) *
          ‖(iteratedFDeriv ℝ j P (π₂ y)).compContinuousLinearMap fun _ => π₂‖
        ≤ (1 + y 2 ^ 2) * (‖iteratedFDeriv ℝ j P (y 2)‖ * ‖π₂‖ ^ j) :=
          mul_le_mul_of_nonneg_left hcomp hw0
      _ = ((1 + y 2 ^ 2) * ‖iteratedFDeriv ℝ j P (y 2)‖) * ‖π₂‖ ^ j := by ring
      _ ≤ CP j * ‖π₂‖ ^ j :=
          mul_le_mul_of_nonneg_right (hCP j (y 2)) (pow_nonneg (norm_nonneg _) _)
  have hf_le : (1 + y 2 ^ 2) * ‖iteratedFDeriv ℝ m f y‖ ≤ C_f := by
    have hmul := norm_iteratedFDeriv_mul_le (n := m) ha cB y (by exact_mod_cast le_top)
    calc (1 + y 2 ^ 2) * ‖iteratedFDeriv ℝ m f y‖
        ≤ (1 + y 2 ^ 2) * ∑ i ∈ Finset.range (m + 1),
            (Nat.choose m i : ℝ) * ‖iteratedFDeriv ℝ i a y‖ * ‖iteratedFDeriv ℝ (m - i) B y‖ :=
          mul_le_mul_of_nonneg_left hmul hw0
      _ = ∑ i ∈ Finset.range (m + 1),
            (Nat.choose m i : ℝ) * ‖iteratedFDeriv ℝ i a y‖ *
              ((1 + y 2 ^ 2) * ‖iteratedFDeriv ℝ (m - i) B y‖) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => by ring
      _ ≤ C_f := by
          unfold C_f
          refine Finset.sum_le_sum fun i _ => ?_
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left (hCa i y hy2) (Nat.cast_nonneg _))
            (hB_jet (m - i))
            (mul_nonneg hw0 (norm_nonneg _))
            (mul_nonneg (Nat.cast_nonneg _) (hCa0 i))
  have hL_le : ‖iteratedFDeriv ℝ m (fun z : Space => (a z * P (z 2)) • v) y‖ ≤
      ‖L‖ * ‖iteratedFDeriv ℝ m f y‖ := by
    rw [hF_eq]
    exact L.norm_iteratedFDeriv_comp_left cf.contDiffAt (by exact_mod_cast le_top)
  calc (1 + y 2 ^ 2) * ‖iteratedFDeriv ℝ m (fun z : Space => (a z * P (z 2)) • v) y‖
      ≤ (1 + y 2 ^ 2) * (‖L‖ * ‖iteratedFDeriv ℝ m f y‖) :=
        mul_le_mul_of_nonneg_left hL_le hw0
    _ = ‖L‖ * ((1 + y 2 ^ 2) * ‖iteratedFDeriv ℝ m f y‖) := by ring
    _ ≤ ‖L‖ * C_f := mul_le_mul_of_nonneg_left hf_le (norm_nonneg _)

theorem wtdHeatJetBdd_e3 (m : ℕ) {R : ℝ} (hR : 0 ≤ R) (c : ℝ) (d : ℕ) {P : ℝ → ℝ}
    (hP : WtdLineJetBdd P) :
    WtdHeatJetBdd m R (fun y : Space => (c * (y 0 ^ 2 + y 1 ^ 2) ^ d * P (y 2)) • Axi.e3) := by
  obtain ⟨ca, Ha⟩ := hfj_poly_w (R ^ 2) c d
  exact wtdHeatJetBdd_smul_const m hR ca Ha hP Axi.e3

theorem wtdHeatJetBdd_hor (m : ℕ) {R : ℝ} (hR : 0 ≤ R) (c : ℝ) (d : ℕ) {P : ℝ → ℝ}
    (hP : WtdLineJetBdd P) :
    WtdHeatJetBdd m R (fun y : Space => (c * (y 0 ^ 2 + y 1 ^ 2) ^ d * P (y 2)) • Axi.hor y) := by
  obtain ⟨ca, Ha⟩ := hfj_poly_w (R ^ 2) c d
  have c0 : ContDiff ℝ ∞ (fun y : Space => y 0) := by fun_prop
  have c1 : ContDiff ℝ ∞ (fun y : Space => y 1) := by fun_prop
  have h0 : HeatJetBdd (R ^ 2) (fun y : Space => y 0) :=
    hfjCoord (W := R ^ 2) 0 (fun y => le_add_of_nonneg_right (sq_nonneg _))
  have h1 : HeatJetBdd (R ^ 2) (fun y : Space => y 1) :=
    hfjCoord (W := R ^ 2) 1 (fun y => le_add_of_nonneg_left (sq_nonneg _))
  have hT0 := wtdHeatJetBdd_smul_const m hR (ca.mul c0) (hfjMul ca c0 Ha h0) hP
    (UnforcedLeray.coordinateVector 0)
  have hT1 := wtdHeatJetBdd_smul_const m hR (ca.mul c1) (hfjMul ca c1 Ha h1) hP
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
  exact wtdHeatJetBdd_add hT0 hT1

theorem heatB1Field_wtdJet (p : Params) (m M : ℕ) :
    WtdHeatJetBdd m p.R (heatB1Field p M) := by
  have hR0 : 0 ≤ p.R := p.R_pos.le
  unfold heatB1Field
  refine wtdHeatJetBdd_sum (Finset.range M) fun d _ => ?_
  exact wtdHeatJetBdd_hor m hR0
    ((ringEps p.R ^ 2 *
        (meanCoeff p.train (d + 1) *
          (p.ν * (2 * ((d + 1 : ℕ) : ℝ)) * (2 * ((d + 1 : ℕ) : ℝ) + 2)))) /
      p.R ^ (2 * d + 1))
    d (wtdLineJetBdd_profileDeriv p.ν_pos (2 * d + 3))

theorem heatB3Field_wtdJet (p : Params) (m M : ℕ) :
    WtdHeatJetBdd m p.R (heatB3Field p M) := by
  have hR0 : 0 ≤ p.R := p.R_pos.le
  unfold heatB3Field
  refine wtdHeatJetBdd_sum (Finset.range M) fun d _ => ?_
  exact wtdHeatJetBdd_e3 m hR0
    ((ringEps p.R ^ 3 *
        (-(meanCoeff p.train (d + 1) *
          p.ν * (2 * ((d + 1 : ℕ) : ℝ)) ^ 2 * (2 * ((d + 1 : ℕ) : ℝ) + 2)))) /
      p.R ^ (2 * d))
    d (wtdLineJetBdd_profileDeriv p.ν_pos (2 * d + 2))

theorem heatA1Field_wtdJet (p : Params) (m M : ℕ) :
    WtdHeatJetBdd m p.R (heatA1Field p M) := by
  have hR0 : 0 ≤ p.R := p.R_pos.le
  unfold heatA1Field
  refine wtdHeatJetBdd_sum (Finset.range (M + 1) ×ˢ Finset.range (M + 1)) fun q _ => ?_
  have h1 : WtdHeatJetBdd m p.R (heatA1Field₁ p q.1 q.2) :=
    wtdHeatJetBdd_hor m hR0
      ((ringEps p.R * (-(meanCoeff p.train q.1 * meanCoeff p.train q.2 * (2 * (q.1 : ℝ) + 2)))) /
        p.R ^ (2 * (q.1 + q.2) + 1))
      (q.1 + q.2)
      (wtdLineJetBdd_mul
        (wtdLineJetBdd_profileDeriv p.ν_pos (2 * q.1))
        (wtdLineJetBdd_profileDeriv p.ν_pos (2 * q.2 + 2)))
  have h2 : WtdHeatJetBdd m p.R (heatA1Field₂ p q.1 q.2) :=
    wtdHeatJetBdd_hor m hR0
      ((ringEps p.R * (meanCoeff p.train q.1 * meanCoeff p.train q.2 * (2 * (q.2 : ℝ) + 1))) /
        p.R ^ (2 * (q.1 + q.2) + 1))
      (q.1 + q.2)
      (wtdLineJetBdd_mul
        (wtdLineJetBdd_profileDeriv p.ν_pos (2 * q.1 + 1))
        (wtdLineJetBdd_profileDeriv p.ν_pos (2 * q.2 + 1)))
  exact wtdHeatJetBdd_add h1 h2

theorem heatPairTermE1_wtdJet {ν : ℝ} (hν : 0 < ν) {R : ℝ} (hR : 0 ≤ R)
    (m : ℕ) (coeff : ℝ) (a b : ℕ) :
    WtdHeatJetBdd m R (BlockB2Sub.heatPairTermE1 ν R coeff a b) := by
  have heq : BlockB2Sub.heatPairTermE1 ν R coeff a b =
      fun z : Space =>
        ((coeff * R⁻¹ ^ (2 * (a + b))) * (z 0 ^ 2 + z 1 ^ 2) ^ (a + b) *
          (UnforcedLeray.B0191.profileDeriv ν (2 * a) (z 2) *
            UnforcedLeray.B0191.profileDeriv ν (2 * b + 1) (z 2))) • Axi.e3 := by
    funext z
    simp [BlockB2Sub.heatPairTermE1, mul_assoc]
  rw [heq]
  exact wtdHeatJetBdd_e3 m hR (coeff * R⁻¹ ^ (2 * (a + b))) (a + b)
    (wtdLineJetBdd_mul
      (wtdLineJetBdd_profileDeriv hν (2 * a))
      (wtdLineJetBdd_profileDeriv hν (2 * b + 1)))

theorem F_heat_B2_wtdJet (p : Params) (m M : ℕ) :
    WtdHeatJetBdd m p.R (BlockB2Sub.F_heat_B2 p M) := by
  have hR0 : 0 ≤ p.R := p.R_pos.le
  unfold BlockB2Sub.F_heat_B2
  refine wtdHeatJetBdd_sum (Finset.range (M + 1)) fun j₁ _ => ?_
  refine wtdHeatJetBdd_sum (Finset.range (M + 1)) fun j₂ _ => ?_
  exact wtdHeatJetBdd_add
    (heatPairTermE1_wtdJet p.ν_pos hR0 m _ j₂ j₁)
    (heatPairTermE1_wtdJet p.ν_pos hR0 m _ j₁ j₂)

/-- Total Cartesian heat field at expansion order `M` for all four mean blocks. -/
def F_heat_total (p : Params) (M : ℕ) (z : Space) : Space :=
  heatB1Field p M z + heatB3Field p M z + heatA1Field p M z + BlockB2Sub.F_heat_B2 p M z

theorem F_heat_total_wtdJet (p : Params) (m M : ℕ) :
    WtdHeatJetBdd m p.R (F_heat_total p M) :=
  wtdHeatJetBdd_add
    (wtdHeatJetBdd_add (wtdHeatJetBdd_add (heatB1Field_wtdJet p m M) (heatB3Field_wtdJet p m M))
      (heatA1Field_wtdJet p m M))
    (F_heat_B2_wtdJet p m M)

/-! ### 2. All-order off-axis `Axi.age R • Axi.Nv R b τ` pointwise jet bound -/

theorem ϱ_rpow_neg_two_add_le_age_all {R : ℝ} (hR : 1 ≤ R) {y : Space}
    (hy : y ∉ Axi.axis) {m i : ℕ} (hi : i ≤ m) :
    Axi.ϱ y ^ (-(2 + (i : ℝ))) ≤ (1 + Axi.age R y) ^ (m + 2) := by
  have hρ : 0 < Axi.ϱ y := Axi.ϱ_pos hy
  have hR0 : R ≠ 0 := by linarith
  have hs : 0 < Axi.age R y := Axi.age_pos hR0 hy
  have h1s : 1 ≤ 1 + Axi.age R y := by linarith
  have hinv0 : 0 ≤ (Axi.ϱ y)⁻¹ := inv_nonneg.2 hρ.le
  have hinv := AxialTailSub.inv_ϱ_le_one_add_age hR hy
  have hexp : -(2 + (i : ℝ)) = -(((2 + i : ℕ) : ℝ)) := by push_cast; ring
  rw [hexp, Real.rpow_neg hρ.le, Real.rpow_natCast, ← inv_pow]
  calc ((Axi.ϱ y)⁻¹) ^ (2 + i)
      ≤ (1 + Axi.age R y) ^ (2 + i) := pow_le_pow_left₀ hinv0 hinv _
    _ ≤ (1 + Axi.age R y) ^ (m + 2) := pow_le_pow_right₀ h1s (by omega)

theorem age_jet_off_axis_upto (R : ℝ) (hR : 0 < R) (m : ℕ) :
    ∃ Ca : ℝ, 0 ≤ Ca ∧ ∀ y : Space, y ∉ Axi.axis → ∀ i ≤ m,
      ‖iteratedFDeriv ℝ i (Axi.age R) y‖ ≤ Ca * Axi.ϱ y ^ (-(2 + (i : ℝ))) := by
  have key : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Space, y ∉ Axi.axis →
      ‖iteratedFDeriv ℝ i (Axi.age R) y‖ ≤ C * Axi.ϱ y ^ (-(2 + (i : ℝ))) := by
    intro i
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · refine ⟨R ^ 2, sq_nonneg R, fun y hy => ?_⟩
      have hp : 0 < Axi.ϱ y := Axi.ϱ_pos hy
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, Axi.age,
        abs_of_nonneg (div_nonneg (sq_nonneg R) (sq_nonneg _)), div_eq_mul_inv]
      have hexp : -(2 + ((0 : ℕ) : ℝ)) = -((2 : ℕ) : ℝ) := by norm_num
      rw [hexp, Real.rpow_neg hp.le, Real.rpow_natCast]
    · obtain ⟨C, hC0, hC⟩ := ageJet R hR i hi
      exact ⟨C, hC0, hC⟩
  choose C hC0 hC using key
  refine ⟨∑ i ∈ Finset.range (m + 1), C i, Finset.sum_nonneg fun i _ => hC0 i, fun y hy i hi => ?_⟩
  have hCi : C i ≤ ∑ j ∈ Finset.range (m + 1), C j :=
    Finset.single_le_sum (f := C) (fun j _ => hC0 j) (Finset.mem_range.2 (by omega))
  exact (hC i y hy).trans
    (mul_le_mul_of_nonneg_right hCi (Real.rpow_nonneg (Axi.ϱ_nonneg y) _))

/-- Pointwise order-`m` spatial jet bound for `w ↦ Axi.age R w • Axi.Nv R b τ w` at every off-axis
point `y ∉ Axi.axis`, with an exponent `K : ℕ` depending only on `m`. -/
theorem age_smul_nv_pt_jet_all (m : ℕ) :
    ∃ K : ℕ, ∀ (R : ℝ), 2 ≤ R → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : ℝ × (ℝ × ℝ) → Axi.Merid), ContDiffOn ℝ ∞ b {w : ℝ × (ℝ × ℝ) | 0 < w.1} →
        ∀ (τ : ℝ) (y : Space), y ∉ Axi.axis →
          ContDiffOn ℝ ∞ (fun w => Axi.age R w • Axi.Nv R b τ w) Axi.axisᶜ ∧
          ‖iteratedFDeriv ℝ m (fun w => Axi.age R w • Axi.Nv R b τ w) y‖ ≤
            C * (1 + Axi.age R y) ^ K * (1 + |Axi.trans R y|) ^ m *
              ∑ l ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖ := by
  choose Cj kj hCj Hj using ringLiftPtJet
  set K_nv : ℕ := ∑ j ∈ Finset.range (m + 1), kj j
  set C_nv : ℝ := ∑ j ∈ Finset.range (m + 1), Cj j
  have hCnv0 : 0 ≤ C_nv := Finset.sum_nonneg fun j _ => (hCj j).le
  refine ⟨K_nv + (m + 2), fun R hR => ?_⟩
  have hR1 : 1 ≤ R := by linarith
  have hRpos : 0 < R := by linarith
  obtain ⟨Ca, hCa0, hCa⟩ := age_jet_off_axis_upto R hRpos m
  set B_comb : ℝ := ∑ i ∈ Finset.range (m + 1), (Nat.choose m i : ℝ)
  have hBcomb0 : 0 ≤ B_comb := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  refine ⟨B_comb * Ca * C_nv, mul_nonneg (mul_nonneg hBcomb0 hCa0) hCnv0, fun b hb τ y hyax => ?_⟩
  have hb' : ContDiffOn ℝ ∞ b (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := by
    rwa [← AxialTailSub.setOf_fst_pos_eq_prod]
  have hAgeS : ContDiffOn ℝ ∞ (Axi.age R) Axi.axisᶜ :=
    contDiffOn_const.div (Axi.contDiffOn_ϱ.pow 2)
      (fun z hz => pow_ne_zero 2 (Axi.ϱ_ne_zero hz))
  have hNvS : ContDiffOn ℝ ∞ (Axi.Nv R b τ) Axi.axisᶜ := (Hj 0 R τ b hR1 hb').1
  refine ⟨hAgeS.smul hNvS, ?_⟩
  have hyS : y ∈ (Axi.axisᶜ : Set Space) := hyax
  have hs : 0 < Axi.age R y := Axi.age_pos hRpos.ne' hyax
  have h1s : 1 ≤ 1 + Axi.age R y := by linarith
  have h1t : 1 ≤ 1 + |Axi.trans R y| := by linarith [abs_nonneg (Axi.trans R y)]
  have hNv_le : ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j (Axi.Nv R b τ) y‖ ≤
        C_nv * (1 + Axi.age R y) ^ K_nv * (1 + |Axi.trans R y|) ^ m *
          ∑ l ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖ := by
    intro j hj
    have hj_mem : j ∈ Finset.range (m + 1) := Finset.mem_range.2 (by omega)
    have hsub : ∑ l ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖ ≤
        ∑ l ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.2 (by omega)) (fun _ _ _ => norm_nonneg _)
    have hsumj0 : 0 ≤ ∑ l ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    have ht_le : (1 + |Axi.trans R y|) ^ j ≤ (1 + |Axi.trans R y|) ^ m :=
      pow_le_pow_right₀ h1t hj
    have hk_le : kj j ≤ K_nv :=
      Finset.single_le_sum (f := kj) (fun _ _ => Nat.zero_le _) hj_mem
    have hk : (1 + Axi.age R y) ^ kj j ≤ (1 + Axi.age R y) ^ K_nv :=
      pow_le_pow_right₀ h1s hk_le
    have hC : Cj j ≤ C_nv :=
      Finset.single_le_sum (f := Cj) (fun l _ => (hCj l).le) hj_mem
    have hfac : Cj j * (1 + Axi.age R y) ^ kj j * (1 + |Axi.trans R y|) ^ j ≤
        C_nv * (1 + Axi.age R y) ^ K_nv * (1 + |Axi.trans R y|) ^ m :=
      mul_le_mul (mul_le_mul hC hk (by positivity) hCnv0) ht_le (by positivity) (by positivity)
    exact ((Hj j R τ b hR1 hb').2 y hyax).trans (mul_le_mul hfac hsub hsumj0 (by positivity))
  have hleib : ‖iteratedFDeriv ℝ m (fun w => Axi.age R w • Axi.Nv R b τ w) y‖ ≤
      ∑ i ∈ Finset.range (m + 1), (Nat.choose m i : ℝ) *
        ‖iteratedFDerivWithin ℝ i (Axi.age R) Axi.axisᶜ y‖ *
        ‖iteratedFDerivWithin ℝ (m - i) (Axi.Nv R b τ) Axi.axisᶜ y‖ := by
    rw [← iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
      (f := fun w => Axi.age R w • Axi.Nv R b τ w) m Axi.isOpen_compl_axis hyS]
    exact norm_iteratedFDerivWithin_smul_le hAgeS hNvS
      Axi.isOpen_compl_axis.uniqueDiffOn hyS (n := m) (by exact_mod_cast le_top)
  calc ‖iteratedFDeriv ℝ m (fun w => Axi.age R w • Axi.Nv R b τ w) y‖
      ≤ ∑ i ∈ Finset.range (m + 1), (Nat.choose m i : ℝ) *
          ‖iteratedFDerivWithin ℝ i (Axi.age R) Axi.axisᶜ y‖ *
          ‖iteratedFDerivWithin ℝ (m - i) (Axi.Nv R b τ) Axi.axisᶜ y‖ := hleib
    _ ≤ ∑ i ∈ Finset.range (m + 1), (Nat.choose m i : ℝ) *
          (Ca * (1 + Axi.age R y) ^ (m + 2) *
            (C_nv * (1 + Axi.age R y) ^ K_nv * (1 + |Axi.trans R y|) ^ m *
              ∑ l ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖)) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi_le : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        rw [iteratedFDerivWithin_of_isOpen i Axi.isOpen_compl_axis hyS,
          iteratedFDerivWithin_of_isOpen (m - i) Axi.isOpen_compl_axis hyS]
        have hA_i : ‖iteratedFDeriv ℝ i (Axi.age R) y‖ ≤ Ca * (1 + Axi.age R y) ^ (m + 2) :=
          (hCa y hyax i hi_le).trans
            (mul_le_mul_of_nonneg_left (ϱ_rpow_neg_two_add_le_age_all hR1 hyax hi_le) hCa0)
        have hB_i := hNv_le (m - i) (Nat.sub_le m i)
        calc (Nat.choose m i : ℝ) * ‖iteratedFDeriv ℝ i (Axi.age R) y‖ *
              ‖iteratedFDeriv ℝ (m - i) (Axi.Nv R b τ) y‖
            = (Nat.choose m i : ℝ) *
                (‖iteratedFDeriv ℝ i (Axi.age R) y‖ *
                  ‖iteratedFDeriv ℝ (m - i) (Axi.Nv R b τ) y‖) := by ring
          _ ≤ (Nat.choose m i : ℝ) *
                ((Ca * (1 + Axi.age R y) ^ (m + 2)) *
                  (C_nv * (1 + Axi.age R y) ^ K_nv * (1 + |Axi.trans R y|) ^ m *
                    ∑ l ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖)) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul hA_i hB_i (norm_nonneg _) (by positivity))
                (Nat.cast_nonneg _)
    _ = B_comb * Ca * C_nv * (1 + Axi.age R y) ^ (K_nv + (m + 2)) * (1 + |Axi.trans R y|) ^ m *
          ∑ l ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖ := by
        rw [← Finset.sum_mul]
        dsimp [B_comb]
        rw [pow_add]
        ring

/-- Off-axis order-`m` partial derivative bound for `rawResidualC p` by the spatial `iteratedFDeriv`
of `w ↦ Axi.age p.R w • Axi.Nv p.R (resChartProfile p) τ w`. -/
theorem norm_iterDyRev_rawResidualC_le_iteratedFDeriv (p : Params)
    (htr : IsBUCTrain p.train) (hR : 2 ≤ p.R)
    {m : ℕ} (β : Fin m → Fin 3) (τ : ℝ) {y : Space} (hy : Axi.ϱ y ≠ 0) :
    ‖iterDyRev β (rawResidualC p) (τ, y)‖ ≤
      ‖iteratedFDeriv ℝ m
        (fun w => Axi.age p.R w • Axi.Nv p.R (resChartProfile p) τ w) y‖ := by
  have hyax : y ∉ Axi.axis := mt (Axi.mem_axis_iff y).mp hy
  have hsm := resChartProfile_contDiffOn p htr
  have hU : IsOpen {z : ℝ × Space | z.2 ∉ Axi.axis} :=
    Axi.isOpen_compl_axis.preimage continuous_snd
  have hRpos : 0 < p.R := by linarith
  have hGsm : ContDiffOn ℝ ∞ (rawResidualC p) {z : ℝ × Space | z.2 ∉ Axi.axis} :=
    (age_smul_Nv_joint_contDiffOn p.R hRpos (resChartProfile p) hsm).congr
      (fun z hz => rawResidualC_eq_off_axis p htr hR z hz)
  have hsb := RawIterEnvSub.norm_iterDyRev_le_slice hU hGsm β (a := τ) (y := y) hyax
  have hslice_eq : iteratedFDeriv ℝ m (fun w => rawResidualC p (τ, w)) y =
      iteratedFDeriv ℝ m
        (fun w => efarRealCLI (Axi.age p.R w • Axi.Nv p.R (resChartProfile p) τ w)) y := by
    have hev : (fun w => rawResidualC p (τ, w)) =ᶠ[𝓝 y]
        (fun w => efarRealCLI (Axi.age p.R w • Axi.Nv p.R (resChartProfile p) τ w)) :=
      Filter.eventuallyEq_of_mem (Axi.isOpen_compl_axis.mem_nhds hyax)
        (fun w hw => rawResidualC_eq_off_axis p htr hR (τ, w) hw)
    exact (hev.iteratedFDeriv ℝ m).eq_of_nhds
  have hrealS : ContDiffOn ℝ ∞
      (fun w => Axi.age p.R w • Axi.Nv p.R (resChartProfile p) τ w) Axi.axisᶜ := by
    have hAgeS : ContDiffOn ℝ ∞ (Axi.age p.R) Axi.axisᶜ :=
      contDiffOn_const.div (Axi.contDiffOn_ϱ.pow 2)
        (fun z hz => pow_ne_zero 2 (Axi.ϱ_ne_zero hz))
    have hgS : ContDiffOn ℝ ∞ (fun z => resChartProfile p (Axi.chart p.R τ z)) Axi.axisᶜ :=
      hsm.comp (clf_chart_contDiffOn p.R τ hRpos) (clf_chart_mapsTo p.R τ hRpos)
    have hNvS : ContDiffOn ℝ ∞ (Axi.Nv p.R (resChartProfile p) τ) Axi.axisᶜ := by
      have hEq : Axi.Nv p.R (resChartProfile p) τ =
          fun z => liftFactor p.R z (resChartProfile p (Axi.chart p.R τ z)) :=
        funext fun z => Nv_eq_liftFactor p.R (resChartProfile p) τ z
      rw [hEq]
      exact (clf_lift_contDiffOn p.R hRpos).clm_apply hgS
    exact hAgeS.smul hNvS
  have hiso := efar_realC_norm
    (fun w => Axi.age p.R w • Axi.Nv p.R (resChartProfile p) τ w) hrealS hyax m
  calc ‖iterDyRev β (rawResidualC p) (τ, y)‖
      ≤ ‖iteratedFDeriv ℝ m (fun w => rawResidualC p (τ, w)) y‖ := hsb
    _ = ‖iteratedFDeriv ℝ m
          (fun w => Axi.age p.R w • Axi.Nv p.R (resChartProfile p) τ w) y‖ := by
        rw [hslice_eq, hiso]

end UnforcedLeray.Short.IIb.RawResidualIteratedLateTailAux
