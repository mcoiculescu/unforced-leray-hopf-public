import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3_1_2_2_2_2
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3_1_1_2_1_1

/-!
# Sub-module for `PartII-b:S3/1/2/2/2/2/1`: Raw and inlet coordinate-jet iterated radial drift in `L⁴(ℝ³)`

Source of record: `the November 2 reference manuscript`
(SP), lines 438-467, 1305-1325, 2543-2559, 2575-2576, and 2594-2610.

## Proved here (zero `sorry`)

1. **All-order pointwise and `L⁴(ℝ³)` bounds for `(spatialRadialDrift^[i])` via iterated derivatives
   (`namespace RawAndInletIteratedDriftSub`)**:
   - `norm_spatialRadialDrift_le_sum_spatialPartial`:
     `‖spatialRadialDrift F y‖ ≤ ∑ l : Fin 3, ‖y‖ * ‖spatialPartial l F y‖`;
   - `norm_iterate_spatialRadialDrift_le_of_iteratedFDeriv`:
     by strong induction on `i : ℕ` combined with
     `BaseIteratedRadialDriftSub.norm_iterate_spatialRadialDrift_dirSpatialJet_le`, bounds
     `‖(spatialRadialDrift^[i]) F y‖ ≤ radDriftConst i * B` whenever
     `‖iteratedFDeriv ℝ m F y‖ * ‖y‖ ^ m ≤ B` for all `m ≤ i`;
   - `norm_iterate_spatialRadialDrift_dirSpatialJet_coordWord_le`:
     bounds `‖(spatialRadialDrift^[i]) (dirSpatialJet F (coordWord α)) y‖ ≤ radDriftConst i * B`
     whenever `‖iteratedFDeriv ℝ (k + m) F y‖ * ‖y‖ ^ m ≤ B` for all `m ≤ i`;
   - `eLpNorm_iterate_spatialRadialDrift_dirSpatialJet_le_of_inv_pow_decay`:
     if `‖iteratedFDeriv ℝ (k + m) F y‖ ≤ C * ((1 + ‖y‖) ^ (m + 1))⁻¹` for all `m ≤ i`, then
     `‖(spatialRadialDrift^[i]) (dirSpatialJet F (coordWord α)) y‖ ≤ radDriftConst i * C * (1 + ‖y‖)⁻¹`
     and hence `eLpNorm ((spatialRadialDrift^[i]) (dirSpatialJet F (coordWord α))) 4 volume ≤ ENNReal.ofReal (radDriftConst i * C * decayK)`;
   - `inv_pow_decay_of_offAxis` and `one_add_norm_pow_mul_sqrt_age_pow_le`:
     all-order off-axis-to-global closure and ring-geometry helpers for inverse-power derivative decay.
2. **Reduction of `RawAndInletCoordJetIteratedRadialDriftL4` (`PartII-b:S3/1/2/2/2/2/1`)**:
   - `RawIteratedInvPowDecay` (`PartII-b:S3/1/2/2/2/2/1/1`):
     `‖iteratedFDeriv ℝ n (p.raw τ) y‖ ≤ C * ((1 + ‖y‖) ^ (n + 1))⁻¹`;
   - `InletIteratedInvPowDecay` (`PartII-b:S3/1/2/2/2/2/1/2`):
     `‖iteratedFDeriv ℝ n (p.inlet l τ) y‖ ≤ C * ((1 + ‖y‖) ^ (n + 1))⁻¹`;
   - `rawAndInletCoordJetIteratedRadialDriftL4_of`: assembles
     `RawAndInletCoordJetIteratedRadialDriftL4` from `RawIteratedInvPowDecay` and
     `InletIteratedInvPowDecay`;
   - `rawIteratedInvSqDecay_of_pow` and `inletIteratedInvSqDecay_of_pow`: specialize the all-order
     inverse-power decay at `n = k + 1` to `RawIteratedInvSqDecay` and `InletIteratedInvSqDecay`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff BigOperators

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03 UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace
  UnforcedLeray.B0411 UnforcedLeray.B0412 UnforcedLeray.Blueprint

namespace RawAndInletIteratedDriftSub

open PhaseDerivStepSub SmoothLeraySliceSub ProjectedEvolutionSub
  RadialDriftL4Sub RadialDriftTowerSub BaseIteratedRadialDriftSub

/-- Recursive combinatoric constant bounding `(spatialRadialDrift^[i]) F y` in terms of
`max_{m ≤ i} ‖iteratedFDeriv ℝ m F y‖ * ‖y‖ ^ m`. -/
def radDriftConst : ℕ → ℝ
  | 0 => 1
  | i + 1 => 3 * (2 : ℝ) ^ i * radDriftConst i

@[simp]
theorem radDriftConst_zero : radDriftConst 0 = 1 := rfl

@[simp]
theorem radDriftConst_succ (i : ℕ) :
    radDriftConst (i + 1) = 3 * (2 : ℝ) ^ i * radDriftConst i := rfl

theorem one_le_radDriftConst : ∀ i : ℕ, 1 ≤ radDriftConst i
  | 0 => le_rfl
  | i + 1 => by
      have hi : 1 ≤ radDriftConst i := one_le_radDriftConst i
      have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ i := one_le_pow₀ (by norm_num)
      rw [radDriftConst_succ]
      nlinarith

theorem radDriftConst_pos (i : ℕ) : 0 < radDriftConst i :=
  lt_of_lt_of_le zero_lt_one (one_le_radDriftConst i)

theorem radDriftConst_nonneg (i : ℕ) : 0 ≤ radDriftConst i :=
  (radDriftConst_pos i).le

theorem radDriftConst_mono : Monotone radDriftConst := by
  refine monotone_nat_of_le_succ fun i => ?_
  have hi : 0 ≤ radDriftConst i := radDriftConst_nonneg i
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ i := one_le_pow₀ (by norm_num)
  rw [radDriftConst_succ]
  nlinarith

/-- Pointwise bound `‖spatialRadialDrift F y‖ ≤ ∑ l : Fin 3, ‖y‖ * ‖spatialPartial l F y‖`. -/
theorem norm_spatialRadialDrift_le_sum_spatialPartial (F : SpatialField) (y : Space) :
    ‖spatialRadialDrift F y‖ ≤ ∑ l : Fin 3, ‖y‖ * ‖spatialPartial l F y‖ := by
  rw [ProjectedEvolutionSub.spatialRadialDrift_eq_sum_coord_spatialPartial F y]
  refine (norm_sum_le Finset.univ _).trans ?_
  refine Finset.sum_le_sum fun l _ => ?_
  rw [norm_smul, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le y l

/-- Pointwise bound on `iteratedFDeriv ℝ s (spatialPartial l F) y` by
`‖iteratedFDeriv ℝ (s + 1) F y‖`. -/
theorem norm_iteratedFDeriv_spatialPartial_le {F : SpatialField} (hF : ContDiff ℝ ∞ F)
    (l : Fin 3) (s : ℕ) (y : Space) :
    ‖iteratedFDeriv ℝ s (spatialPartial l F) y‖ ≤ ‖iteratedFDeriv ℝ (s + 1) F y‖ := by
  have h := JointSmoothSub.norm_iteratedFDeriv_dirSpatialJet_le hF [coordinateVector l] s y
  simpa [spatialPartial, coordinateVector, RadialDriftL4Sub.norm_coordinateVector] using h

/-- At the origin `y = 0`, `(spatialRadialDrift^[i + 1]) F 0 = 0`. -/
theorem iterate_spatialRadialDrift_succ_apply_zero (i : ℕ) (F : SpatialField) :
    (spatialRadialDrift^[i + 1]) F 0 = 0 := by
  rw [Function.iterate_succ_apply']
  change fderiv ℝ ((spatialRadialDrift^[i]) F) 0 0 = 0
  exact map_zero _

/-- All-order pointwise bound on `(spatialRadialDrift^[i]) F y` in terms of
`‖iteratedFDeriv ℝ m F y‖ * ‖y‖ ^ m` for `m ≤ i`. -/
theorem norm_iterate_spatialRadialDrift_le_of_iteratedFDeriv
    (i : ℕ) {F : SpatialField} (hF : ContDiff ℝ ∞ F) (y : Space)
    {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ m ≤ i, ‖iteratedFDeriv ℝ m F y‖ * ‖y‖ ^ m ≤ B) :
    ‖(spatialRadialDrift^[i]) F y‖ ≤ radDriftConst i * B := by
  induction i using Nat.strong_induction_on generalizing F B with
  | h n ih =>
    rcases n with _ | i
    · rw [Function.iterate_zero_apply, radDriftConst_zero, one_mul]
      have h0 := hB 0 le_rfl
      rwa [norm_iteratedFDeriv_zero, pow_zero, mul_one] at h0
    · by_cases hy0 : y = 0
      · subst hy0
        rw [iterate_spatialRadialDrift_succ_apply_zero, norm_zero]
        exact mul_nonneg (radDriftConst_nonneg (i + 1)) hB0
      · have hy : 0 < ‖y‖ := norm_pos_iff.2 hy0
        let B₁ : ℝ := B / ‖y‖
        have hB₁0 : 0 ≤ B₁ := div_nonneg hB0 hy.le
        have hpart : ∀ l : Fin 3,
            ‖spatialPartial l ((spatialRadialDrift^[i]) F) y‖ ≤
              (2 : ℝ) ^ i * (radDriftConst i * B₁) := by
          intro l
          have hFl : ContDiff ℝ ∞ (spatialPartial l F) :=
            RadialDriftTowerSub.contDiff_infty_spatialPartial hF l
          have hFl_deriv : ∀ s ≤ i,
              ‖iteratedFDeriv ℝ s (spatialPartial l F) y‖ * ‖y‖ ^ s ≤ B₁ := by
            intro s hs
            have h1 : ‖iteratedFDeriv ℝ s (spatialPartial l F) y‖ * ‖y‖ ^ s ≤
                ‖iteratedFDeriv ℝ (s + 1) F y‖ * ‖y‖ ^ s :=
              mul_le_mul_of_nonneg_right
                (norm_iteratedFDeriv_spatialPartial_le hF l s y) (pow_nonneg hy.le s)
            have h2 : ‖iteratedFDeriv ℝ (s + 1) F y‖ * ‖y‖ ^ s =
                (‖iteratedFDeriv ℝ (s + 1) F y‖ * ‖y‖ ^ (s + 1)) / ‖y‖ := by
              rw [pow_succ, ← mul_assoc, mul_div_cancel_right₀ _ hy.ne']
            exact h1.trans (h2.trans_le (div_le_div_of_nonneg_right (hB (s + 1) (by omega)) hy.le))
          have hFl_rad : ∀ r ≤ i + 0,
              ‖(spatialRadialDrift^[r]) (dirSpatialJet F [coordinateVector l]) y‖ ≤
                radDriftConst i * B₁ := by
            intro r hr
            have hr' : r ≤ i := by omega
            have hih : ‖(spatialRadialDrift^[r]) (spatialPartial l F) y‖ ≤
                radDriftConst r * B₁ :=
              ih r (Nat.lt_succ_of_le hr') hFl hB₁0 (fun s hs => hFl_deriv s (hs.trans hr'))
            exact hih.trans (mul_le_mul_of_nonneg_right (radDriftConst_mono hr') hB₁0)
          have hcomm :=
            BaseIteratedRadialDriftSub.norm_iterate_spatialRadialDrift_dirSpatialJet_le
              hF [EuclideanSpace.single l (1 : ℝ)] y i 0
              (mul_nonneg (radDriftConst_nonneg i) hB₁0) hFl_rad
          have hlen : (1 + ([EuclideanSpace.single l (1 : ℝ)].length : ℝ)) = 2 := by norm_num
          rw [Function.iterate_zero_apply, hlen] at hcomm
          exact hcomm
        rw [Function.iterate_succ_apply']
        calc ‖spatialRadialDrift ((spatialRadialDrift^[i]) F) y‖
            ≤ ∑ l : Fin 3, ‖y‖ * ‖spatialPartial l ((spatialRadialDrift^[i]) F) y‖ :=
              norm_spatialRadialDrift_le_sum_spatialPartial ((spatialRadialDrift^[i]) F) y
          _ ≤ ∑ _l : Fin 3, ‖y‖ * ((2 : ℝ) ^ i * (radDriftConst i * B₁)) :=
              Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hpart l) hy.le
          _ = radDriftConst (i + 1) * B := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
                Nat.cast_ofNat, radDriftConst_succ]
              dsimp [B₁]
              calc (3 : ℝ) * (‖y‖ * ((2 : ℝ) ^ i * (radDriftConst i * (B / ‖y‖))))
                  = 3 * (2 : ℝ) ^ i * radDriftConst i * (‖y‖ * (B / ‖y‖)) := by ring
                _ = 3 * (2 : ℝ) ^ i * radDriftConst i * B := by
                    rw [mul_div_cancel₀ B hy.ne']

/-- Pointwise bound on `(spatialRadialDrift^[i]) (dirSpatialJet F (coordWord α)) y` in terms of
`‖iteratedFDeriv ℝ (k + m) F y‖ * ‖y‖ ^ m` for `m ≤ i`. -/
theorem norm_iterate_spatialRadialDrift_dirSpatialJet_coordWord_le
    (i : ℕ) {F : SpatialField} (hF : ContDiff ℝ ∞ F) {k : ℕ} (α : Fin k → Fin 3)
    (y : Space) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ m ≤ i, ‖iteratedFDeriv ℝ (k + m) F y‖ * ‖y‖ ^ m ≤ B) :
    ‖(spatialRadialDrift^[i]) (dirSpatialJet F (PhaseDerivStepSub.coordWord α)) y‖ ≤
      radDriftConst i * B := by
  have hjet : ContDiff ℝ ∞ (dirSpatialJet F (PhaseDerivStepSub.coordWord α)) :=
    JointSmoothSub.contDiff_infty_dirSpatialJet hF (PhaseDerivStepSub.coordWord α)
  refine norm_iterate_spatialRadialDrift_le_of_iteratedFDeriv i hjet y hB0 fun m hm => ?_
  have h1 := JointSmoothSub.norm_iteratedFDeriv_dirSpatialJet_le hF
    (PhaseDerivStepSub.coordWord α) m y
  rw [RadialDriftL4Sub.coordWord_length, RadialDriftL4Sub.coordWord_norm_prod, mul_one,
    add_comm m k] at h1
  exact (mul_le_mul_of_nonneg_right h1 (pow_nonneg (norm_nonneg y) m)).trans (hB m hm)

/-- If `F : SpatialField` is smooth and for every `m ≤ i` its `(k + m)`-th derivative satisfies
`‖iteratedFDeriv ℝ (k + m) F y‖ ≤ C * ((1 + ‖y‖) ^ (m + 1))⁻¹`, then
`eLpNorm ((spatialRadialDrift^[i]) (dirSpatialJet F (coordWord α))) 4 volume ≤ ENNReal.ofReal (radDriftConst i * C * decayK)`. -/
theorem eLpNorm_iterate_spatialRadialDrift_dirSpatialJet_le_of_inv_pow_decay
    (i : ℕ) {F : SpatialField} (hF : ContDiff ℝ ∞ F) {k : ℕ} (α : Fin k → Fin 3)
    {C : ℝ} (hC : 0 ≤ C)
    (hDecay : ∀ m ≤ i, ∀ y : Space,
      ‖iteratedFDeriv ℝ (k + m) F y‖ ≤ C * ((1 + ‖y‖) ^ (m + 1))⁻¹) :
    eLpNorm ((spatialRadialDrift^[i])
      (dirSpatialJet F (PhaseDerivStepSub.coordWord α))) 4 volume ≤
      ENNReal.ofReal (radDriftConst i * C * RadialDriftL4Sub.decayK) := by
  refine RadialDriftL4Sub.eLpNorm_le_of_decay _
    (mul_nonneg (radDriftConst_nonneg i) hC) fun y => ?_
  have hp : 0 < 1 + ‖y‖ := by positivity
  have hB0 : 0 ≤ C * (1 + ‖y‖)⁻¹ := mul_nonneg hC (inv_nonneg.2 hp.le)
  rw [mul_assoc]
  refine norm_iterate_spatialRadialDrift_dirSpatialJet_coordWord_le i hF α y hB0 fun m hm => ?_
  have hy : ‖y‖ ^ m ≤ (1 + ‖y‖) ^ m :=
    pow_le_pow_left₀ (norm_nonneg y) (by linarith) m
  have hpow : (1 + ‖y‖) ^ m ≠ 0 := pow_ne_zero m hp.ne'
  calc ‖iteratedFDeriv ℝ (k + m) F y‖ * ‖y‖ ^ m
      ≤ (C * ((1 + ‖y‖) ^ (m + 1))⁻¹) * (1 + ‖y‖) ^ m :=
        mul_le_mul (hDecay m hm y) hy (pow_nonneg (norm_nonneg y) m)
          (mul_nonneg hC (inv_nonneg.2 (pow_nonneg hp.le (m + 1))))
    _ = C * (1 + ‖y‖)⁻¹ := by
        rw [pow_succ', mul_inv, mul_assoc, mul_assoc, inv_mul_cancel₀ hpow, mul_one]

/-- Off-axis weighted derivative bound of arbitrary power `r : ℕ` implies global inverse-power
derivative decay for any smooth field `V : Space → Space` agreeing off the axis `Axi.axis` with
`G : Space → Space`. -/
theorem inv_pow_decay_of_offAxis {V G : Space → Space} {m r : ℕ} {C : ℝ}
    (hV : ContDiff ℝ ∞ V)
    (hoff : ∀ y : Space, y ∉ Axi.axis → V y = G y)
    (hG : ∀ y : Space, y ∉ Axi.axis → (1 + ‖y‖) ^ r * ‖iteratedFDeriv ℝ m G y‖ ≤ C) :
    ∀ y : Space, ‖iteratedFDeriv ℝ m V y‖ ≤ C * ((1 + ‖y‖) ^ r)⁻¹ := by
  have hopen : IsOpen {y : Space | y ∉ Axi.axis} := by
    have h1 : {y : Space | y ∉ Axi.axis} = {y : Space | Axi.ϱ y ≠ 0} := by
      ext y
      simp [Axi.mem_axis_iff]
    rw [h1]
    exact isOpen_ne_fun Axi.continuous_ϱ continuous_const
  have hcl : IsClosed {y : Space | (1 + ‖y‖) ^ r * ‖iteratedFDeriv ℝ m V y‖ ≤ C} := by
    refine isClosed_le ?_ continuous_const
    exact ((continuous_const.add continuous_norm).pow r).mul
      (hV.continuous_iteratedFDeriv (m := m) (by exact_mod_cast le_top)).norm
  have hsub :
      {y : Space | y ∉ Axi.axis} ⊆
        {y : Space | (1 + ‖y‖) ^ r * ‖iteratedFDeriv ℝ m V y‖ ≤ C} := by
    intro y hy
    have hev : V =ᶠ[𝓝 y] G :=
      Filter.eventuallyEq_of_mem (hopen.mem_nhds hy) (fun z hz => hoff z hz)
    show (1 + ‖y‖) ^ r * ‖iteratedFDeriv ℝ m V y‖ ≤ C
    rw [(hev.iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds]
    exact hG y hy
  intro y
  have hy_cl : y ∈ closure {z : Space | z ∉ Axi.axis} :=
    UnforcedLeray.Cons.C03.dense_compl_axis y
  have hle : (1 + ‖y‖) ^ r * ‖iteratedFDeriv ℝ m V y‖ ≤ C :=
    (hcl.closure_subset_iff.2 hsub) hy_cl
  have hpos : 0 < (1 + ‖y‖) ^ r := by positivity
  rw [← le_div_iff₀' hpos, div_eq_mul_inv] at hle
  exact hle

/-- All-order off-axis ring geometry bound: for `0 < R`, `0 ≤ S`, `y ∉ Axi.axis`, and
`Axi.age R y ≤ S`, `(1 + ‖y‖) ^ r * √(Axi.age R y) ^ r ≤ (1 + S + R) ^ r * (1 + |Axi.trans R y|) ^ r`. -/
theorem one_add_norm_pow_mul_sqrt_age_pow_le (r : ℕ) {R S : ℝ} (hR : 0 < R) (hS : 0 ≤ S)
    {y : Space} (hy : y ∉ Axi.axis) (hage : Axi.age R y ≤ S) :
    (1 + ‖y‖) ^ r * √(Axi.age R y) ^ r ≤ (1 + S + R) ^ r * (1 + |Axi.trans R y|) ^ r := by
  have h := RawAndInletDriftL4Sub.one_add_norm_mul_sqrt_age_le hR hS hy hage
  have h0 : 0 ≤ (1 + ‖y‖) * √(Axi.age R y) := by positivity
  have hpow : ((1 + ‖y‖) * √(Axi.age R y)) ^ r ≤ ((1 + S + R) * (1 + |Axi.trans R y|)) ^ r :=
    pow_le_pow_left₀ h0 h r
  rwa [mul_pow, mul_pow] at hpow

end RawAndInletIteratedDriftSub

/-- **Leaf 1 (`PartII-b:S3/1/2/2/2/2/1/1`, `RawIteratedInvPowDecay`)**
(`the November 2 reference manuscript`,
lines 438-467, 1305-1325, 2543-2551, 2575-2576, 2594-2610): in the background regime for small `ν`,
for every derivative order `n : ℕ` there is `C ≥ 0` such that for all `τ : ℝ` and `y : Space`,
`‖iteratedFDeriv ℝ n (p.raw τ) y‖ ≤ C * ((1 + ‖y‖) ^ (n + 1))⁻¹`.
Composed by task `PartII-b:S3/1/2/2/2/2/1` via `rawAndInletCoordJetIteratedRadialDriftL4_of`. -/
def RawIteratedInvPowDecay : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm →
    ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ContDiff ℝ ∞ (fun x : ℝ × Space => p.raw x.1 x.2) →
      (Blueprint.IsBoundedBackground p.raw ∧ ∀ τ, IsSolenoidal (p.raw τ)) →
      ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℝ) (y : Space),
        ‖iteratedFDeriv ℝ n (p.raw τ) y‖ ≤ C * ((1 + ‖y‖) ^ (n + 1))⁻¹

/-- **Leaf 2 (`PartII-b:S3/1/2/2/2/2/1/2`, `InletIteratedInvPowDecay`)**
(`the November 2 reference manuscript`,
lines 2347-2369, 2543-2551, 2575-2576, 2594-2610): in the background regime for small `ν`,
for every derivative order `n : ℕ` there is `C ≥ 0` such that for all `l : Fin 2`, `τ : ℝ`, and
`y : Space`, `‖iteratedFDeriv ℝ n (p.inlet l τ) y‖ ≤ C * ((1 + ‖y‖) ^ (n + 1))⁻¹`.
Composed by task `PartII-b:S3/1/2/2/2/2/1` via `rawAndInletCoordJetIteratedRadialDriftL4_of`. -/
def InletIteratedInvPowDecay : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm →
    ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      (∀ l : Fin 2, ContDiff ℝ ∞ (fun x : ℝ × Space => p.inlet l x.1 x.2)) →
      (∀ l : Fin 2, Blueprint.IsBoundedBackground (p.inlet l) ∧
        ∀ τ, IsSolenoidal (p.inlet l τ)) →
      ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (l : Fin 2) (τ : ℝ) (y : Space),
        ‖iteratedFDeriv ℝ n (p.inlet l τ) y‖ ≤ C * ((1 + ‖y‖) ^ (n + 1))⁻¹

/-- Conditional assembly of `RawAndInletCoordJetIteratedRadialDriftL4` (`PartII-b:S3/1/2/2/2/2/1`)
from `RawIteratedInvPowDecay` (`PartII-b:S3/1/2/2/2/2/1/1`) and `InletIteratedInvPowDecay`
(`PartII-b:S3/1/2/2/2/2/1/2`) via
`RawAndInletIteratedDriftSub.eLpNorm_iterate_spatialRadialDrift_dirSpatialJet_le_of_inv_pow_decay`. -/
theorem rawAndInletCoordJetIteratedRadialDriftL4_of
    (hRawDecay : RawIteratedInvPowDecay)
    (hInletDecay : InletIteratedInvPowDecay) :
    RawAndInletCoordJetIteratedRadialDriftL4 := by
  intro Sig lam q hSig hlam dm dp hdm
  obtain ⟨ν₁, hν₁, hR⟩ := hRawDecay Sig lam q hSig hlam dm dp hdm
  obtain ⟨ν₂, hν₂, hI⟩ := hInletDecay Sig lam q hSig hlam dm dp hdm
  refine ⟨min ν₁ ν₂, lt_min hν₁ hν₂, ?_⟩
  intro p d hReg hν hAge hMode hRawCD hInCD hRaw hInlet i k α
  choose C_R hCR0 hCR using
    hR p d hReg (hν.trans (min_le_left _ _)) hAge hMode hRawCD hRaw
  choose C_I hCI0 hCI using
    hI p d hReg (hν.trans (min_le_right _ _)) hAge hMode hInCD hInlet
  let C : ℝ := ∑ m ∈ Finset.range (i + 1), max (C_R (k + m)) (C_I (k + m))
  have hC0 : 0 ≤ C :=
    Finset.sum_nonneg fun m _ => le_trans (hCR0 (k + m)) (le_max_left _ _)
  have hK0 : 0 ≤ RadialDriftL4Sub.decayK := RadialDriftL4Sub.decayK_nonneg
  have hRad0 : 0 ≤ RawAndInletIteratedDriftSub.radDriftConst i :=
    RawAndInletIteratedDriftSub.radDriftConst_nonneg i
  refine ⟨RawAndInletIteratedDriftSub.radDriftConst i * C * RadialDriftL4Sub.decayK,
    mul_nonneg (mul_nonneg hRad0 hC0) hK0, ?_⟩
  intro τ
  have hRawSlice : ContDiff ℝ ∞ (p.raw τ) :=
    PhaseDerivStepSub.contDiff_slice_of_joint (F := p.raw) hRawCD τ
  have hInSlice : ∀ l : Fin 2, ContDiff ℝ ∞ (p.inlet l τ) :=
    fun l => PhaseDerivStepSub.contDiff_slice_of_joint (F := p.inlet l) (hInCD l) τ
  have hpow_mono : ∀ (m : ℕ) (y : Space),
      ((1 + ‖y‖) ^ (k + m + 1))⁻¹ ≤ ((1 + ‖y‖) ^ (m + 1))⁻¹ := by
    intro m y
    have hp1 : 1 ≤ 1 + ‖y‖ := le_add_of_nonneg_right (norm_nonneg y)
    have hp0 : 0 < (1 + ‖y‖) ^ (m + 1) := by positivity
    exact inv_anti₀ hp0 (pow_le_pow_right₀ hp1 (by omega))
  have hmax_le_C : ∀ m ≤ i, max (C_R (k + m)) (C_I (k + m)) ≤ C := by
    intro m hm
    have hm_mem : m ∈ Finset.range (i + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le hm)
    exact Finset.single_le_sum (f := fun j => max (C_R (k + j)) (C_I (k + j)))
      (fun j _ => le_trans (hCR0 (k + j)) (le_max_left _ _)) hm_mem
  refine ⟨?_, ?_⟩
  · refine RawAndInletIteratedDriftSub.eLpNorm_iterate_spatialRadialDrift_dirSpatialJet_le_of_inv_pow_decay
      i hRawSlice α hC0 fun m hm y => ?_
    have hle_C : C_R (k + m) ≤ C :=
      (le_max_left (C_R (k + m)) (C_I (k + m))).trans (hmax_le_C m hm)
    exact (hCR (k + m) τ y).trans
      (mul_le_mul hle_C (hpow_mono m y) (by positivity) hC0)
  · intro l
    refine RawAndInletIteratedDriftSub.eLpNorm_iterate_spatialRadialDrift_dirSpatialJet_le_of_inv_pow_decay
      i (hInSlice l) α hC0 fun m hm y => ?_
    have hle_C : C_I (k + m) ≤ C :=
      (le_max_right (C_R (k + m)) (C_I (k + m))).trans (hmax_le_C m hm)
    exact (hCI (k + m) l τ y).trans
      (mul_le_mul hle_C (hpow_mono m y) (by positivity) hC0)

/-- `RawIteratedInvPowDecay` at `n = k + 1` implies `RawIteratedInvSqDecay`
(`PartII-b:S3/1/1/2/1/1/1`). -/
theorem rawIteratedInvSqDecay_of_pow (h : RawIteratedInvPowDecay) :
    RawIteratedInvSqDecay := by
  intro Sig lam q hSig hlam dm dp hdm
  obtain ⟨ν₀, hν₀, hR⟩ := h Sig lam q hSig hlam dm dp hdm
  refine ⟨ν₀, hν₀, fun p d hReg hν hAge hMode hRawCD hRaw k => ?_⟩
  obtain ⟨C, hC0, hC⟩ := hR p d hReg hν hAge hMode hRawCD hRaw (k + 1)
  refine ⟨C, hC0, fun τ y => (hC τ y).trans ?_⟩
  refine mul_le_mul_of_nonneg_left ?_ hC0
  have hp1 : 1 ≤ 1 + ‖y‖ := le_add_of_nonneg_right (norm_nonneg y)
  have hp0 : 0 < (1 + ‖y‖) ^ 2 := by positivity
  exact inv_anti₀ hp0 (pow_le_pow_right₀ hp1 (by omega))

/-- `InletIteratedInvPowDecay` at `n = k + 1` implies `InletIteratedInvSqDecay`
(`PartII-b:S3/1/1/2/1/1/2`). -/
theorem inletIteratedInvSqDecay_of_pow (h : InletIteratedInvPowDecay) :
    InletIteratedInvSqDecay := by
  intro Sig lam q hSig hlam dm dp hdm
  obtain ⟨ν₀, hν₀, hI⟩ := h Sig lam q hSig hlam dm dp hdm
  refine ⟨ν₀, hν₀, fun p d hReg hν hAge hMode hInCD hInlet k => ?_⟩
  obtain ⟨C, hC0, hC⟩ := hI p d hReg hν hAge hMode hInCD hInlet (k + 1)
  refine ⟨C, hC0, fun l τ y => (hC l τ y).trans ?_⟩
  refine mul_le_mul_of_nonneg_left ?_ hC0
  have hp1 : 1 ≤ 1 + ‖y‖ := le_add_of_nonneg_right (norm_nonneg y)
  have hp0 : 0 < (1 + ‖y‖) ^ 2 := by positivity
  exact inv_anti₀ hp0 (pow_le_pow_right₀ hp1 (by omega))

end UnforcedLeray.Short.IIb

end
