import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1Org
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymNuEps
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# `PartIII-b:C/rep/5/1/2/org`: the age-bin analysis of the thin velocity (stream transition leaf)

Source `the November 2 reference manuscript` 5569-5600, 5618-5619.  The thin-source
velocity is estimated bin by bin in the output age (5585-5593): logarithmic bins of width `h < δ/2`,
bin upper age `s_j`, normalized velocity on the bin `≤ C ε^{3/2}(s_j^{1/2}+s_j^{3/4})‖T‖_{Z₁}` (with
the gain growth `e^{γ/(10ν)}`, 5601-5605); summing the geometric bins down to age zero (5594-5600)
gives the operator bound `P_ν S^k ε^{3/2}`.

The file is generic in the operator family `Θ` (the far mask `S_μ - S_N` or the stream transition
`Y = (wardOps).1`), so that both leaves share it.  Contents:

* the bins `binUpper`, `binSet`, the bin norm `binNorm` (an `eLpNorm` on the restricted body
  measure of `VelG`);
* the Props `PerBinVelocity` (5585-5593), `OutSupported` (the output lives below the cut `S`),
  `BinTriangle` (bins to norm), `ThinMassBound` (5571-5575);
* the real-analysis bin summation (proved) and the assembly `thinAt_of_bins` (proved), giving
  `AgeVelWardThin` / `AgeVelSopThin` (with `k₀ = 0`: `ε^{3/2}S^{3/4} ≤ 1` since `b < 1`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. Logarithmic age bins -/

/-- Upper age `s_j = S e^{-h j}` of the `j`-th logarithmic bin (source 5585-5586). -/
def binUpper (S h : ℝ) (j : ℕ) : ℝ := S * Real.exp (-(h * j))

/-- The `j`-th bin `(s_{j+1}, s_j]` of ages in the chart (source 5585-5586); the bins partition
the ages `(0, S]`. -/
def binSet (S h : ℝ) (j : ℕ) : Set Chart :=
  {p | binUpper S h (j + 1) < p.1 ∧ p.1 ≤ binUpper S h j}

/-- The `L²` norm of a body velocity on the `j`-th age bin (normalized body norm, with gain). -/
def binNorm (c γ ν S h : ℝ) (j : ℕ) (φ : VelG c γ ν) : ℝ :=
  (eLpNorm (φ : Chart → Merid) 2 ((bodyMeasure c γ ν).restrict (binSet S h j))).toReal

/-- The bin width `h = δ/4 < δ/2` (source 5585-5586). -/
def ReturnConsts.hbin (K : ReturnConsts) : ℝ := K.δ / 4

theorem binUpper_rpow (S h p : ℝ) (j : ℕ) (hS : 0 ≤ S) :
    binUpper S h j ^ p = S ^ p * (Real.exp (-(h * p))) ^ j := by
  unfold binUpper
  rw [Real.mul_rpow hS (Real.exp_pos _).le, ← Real.exp_mul, ← Real.exp_nat_mul]
  congr 2
  ring

theorem exp_neg_mul_lt_one {h p : ℝ} (hh : 0 < h) (hp : 0 < p) : Real.exp (-(h * p)) < 1 := by
  have : -(h * p) < 0 := by nlinarith
  simpa using Real.exp_lt_exp.2 this

/-- Geometric sum of the `p`-th powers of the bin ages. -/
theorem hasSum_binUpper_rpow (S h p : ℝ) (hS : 0 ≤ S) (hh : 0 < h) (hp : 0 < p) :
    HasSum (fun j : ℕ => binUpper S h j ^ p) (S ^ p * (1 - Real.exp (-(h * p)))⁻¹) := by
  have hr : Real.exp (-(h * p)) < 1 := exp_neg_mul_lt_one hh hp
  have := (hasSum_geometric_of_lt_one (Real.exp_pos _).le hr).mul_left (S ^ p)
  have e : (fun j : ℕ => binUpper S h j ^ p) = fun j : ℕ => S ^ p * Real.exp (-(h * p)) ^ j :=
    funext fun j => binUpper_rpow S h p j hS
  rw [e]
  exact this

/-- The bin constant `K_h = (1 - e^{-h/2})⁻¹ + (1 - e^{-3h/4})⁻¹`. -/
def binK (h : ℝ) : ℝ :=
  (1 - Real.exp (-(h * (1 / 2))))⁻¹ + (1 - Real.exp (-(h * (3 / 4))))⁻¹

theorem binK_nonneg {h : ℝ} (hh : 0 < h) : 0 ≤ binK h := by
  have h1 : ∀ p : ℝ, 0 < p → 0 ≤ (1 - Real.exp (-(h * p)))⁻¹ := fun p hp => by
    have := exp_neg_mul_lt_one hh hp
    exact inv_nonneg.2 (by linarith)
  exact add_nonneg (h1 _ (by norm_num)) (h1 _ (by norm_num))

/-- **Geometric bin summation** (source 5594-5600): the bin bounds
`M (s_j^{1/2} + s_j^{3/4})` are summable with sum `≤ M (S^{1/2} + S^{3/4}) K_h`. -/
theorem binSum_bound (S h M : ℝ) (hS : 0 ≤ S) (hh : 0 < h) (hM : 0 ≤ M) :
    Summable (fun j : ℕ => M * (binUpper S h j ^ (1 / 2 : ℝ) + binUpper S h j ^ (3 / 4 : ℝ))) ∧
    ∑' j : ℕ, M * (binUpper S h j ^ (1 / 2 : ℝ) + binUpper S h j ^ (3 / 4 : ℝ)) ≤
      M * (S ^ (1 / 2 : ℝ) * (1 - Real.exp (-(h * (1 / 2))))⁻¹ +
        S ^ (3 / 4 : ℝ) * (1 - Real.exp (-(h * (3 / 4))))⁻¹) := by
  have h1 := hasSum_binUpper_rpow S h (1 / 2) hS hh (by norm_num)
  have h2 := hasSum_binUpper_rpow S h (3 / 4) hS hh (by norm_num)
  have h3 := (h1.add h2).mul_left M
  exact ⟨h3.summable, h3.tsum_eq.le⟩

/-- `ε^{3/2} S^{p} ≤ 1` for `S = ε^{-b}`, `0 < ε ≤ 1`, `b p ≤ 3/2`. -/
theorem eps_mul_cut_le_one {ε b p : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hbp : b * p ≤ 3 / 2) :
    ε ^ (3 / 2 : ℝ) * (ε ^ (-b)) ^ p ≤ 1 := by
  rw [← Real.rpow_mul hε.le, ← Real.rpow_add hε]
  exact Real.rpow_le_one hε.le hε1 (by linarith)

/-! ## 2. The estimates stated over the real objects -/

/-- A family of thin-source operators: one operator `LStr → LVel` for each level `n` and `z`
(the far mask `S_μ - S_N`, or the stream transition `Y = (wardOps).1`). -/
abbrev ThinFam :=
  ∀ (D : SeqData) (n : ℕ) (_z : ℝ), LStr D.Pl D.K (D.level n) →L[ℝ] LVel D.Pl (D.level n)

/-- The far mask `S_far = S_μ - S_N` (source 3902-3912, 5303-5316). -/
def sopThinFam : ThinFam := fun D n z =>
  Sop D.Pl D.K (D.level n) (D.mu n z) - SNop D.Pl D.K (D.level n) (D.mu n z)

/-- The stream transition `Y = (wardOps).1` (source 4161-4303, 5569-5600). -/
def wardThinFam : ThinFam := fun D n z => (wardOps D.Pl D.K (D.level n) (D.mu n z)).1

/-- **Thin mass bound** (source 5571-5575): for an unweighted thin stress `f ∈ Z₁` and `a > 0`, the
old physical mass (`L¹` norm of `f` on the ages `t > a` for the physical measure `t^{-3/2} dς`,
divided by `πR²`) is `≤ C (a^{-3/4} + a^{-1/2}) ‖f‖_{Z₁}`; transverse Cauchy-Schwarz contributes
`(1+t)^{1/4}` and the age integral is `∫_a^∞ t^{-5/2}(1+t)^{1/2} dt`. -/
def ThinMassBound (mZ : ℝ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ c : ℝ, 1 ≤ c → ∀ a : ℝ, 0 < a → ∀ f : Z1sp c mZ,
    ∫⁻ p in {p : Chart | a < p.1}, ‖(f : Chart → Ten3) p‖ₑ ∂(ageμ c (-3 / 2)) ≤
      ENNReal.ofReal (C * c ^ k * (a ^ (-(3 / 4 : ℝ)) + a ^ (-(1 / 2 : ℝ)))) * ‖f‖ₑ

/-- **Bins to norm**: a body velocity vanishing above the cut `S` has norm at most the sum of any
summable majorant of its bin norms (the bins partition `(0, S]`; the `L²` norm of the pieces adds
in quadrature, hence is at most their sum). -/
def BinTriangle : Prop :=
  ∀ (c γ ν S h : ℝ), 0 < h → ∀ φ : VelG c γ ν,
    (∀ᵐ p ∂(bodyMeasure c γ ν), S < p.1 → (φ : Chart → Merid) p = 0) →
    ∀ B : ℕ → ℝ, Summable B → (∀ j, binNorm c γ ν S h j φ ≤ B j) → ‖φ‖ ≤ ∑' j, B j

namespace SeqData

/-- **Per-bin normalized velocity** (source 5585-5593, 5601-5605): on each output bin `j` of upper
age `s_j = S e^{-hj}` (`S = ε^{-b}`, `h = δ/4`) the thin velocity is bounded by
`C ε^{3/2}(s_j^{1/2}+s_j^{3/4})‖T‖` times the gain growth `e^{γ/(10ν)}` (the early-source margin of
5601-5605) and `P_ν`. -/
def PerBinVelocity (D : SeqData) (Θ : ThinFam) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ∀ T : LStr D.Pl D.K (D.level n), ∀ j : ℕ,
      binNorm (cOf (D.level n).ν) (gRate D.Pl) (D.level n).ν ((D.level n).Scut D.K)
          D.K.hbin j (Θ D n z (thinPart T)) ≤
        C * (D.level n).ν⁻¹ ^ k * Real.exp ((gRate D.Pl / 10) / (D.level n).ν) *
          (D.level n).ε ^ (3 / 2 : ℝ) *
          (binUpper ((D.level n).Scut D.K) D.K.hbin j ^ (1 / 2 : ℝ) +
            binUpper ((D.level n).Scut D.K) D.K.hbin j ^ (3 / 4 : ℝ)) * ‖T‖

/-- The output of `Θ` on thin sources vanishes above the cut `S = ε^{-b}` (the far mask carries
`1_{s<S}`, 3905-3912; the stream cutoff `χ_y` vanishes beyond `1/ν`, 4164). -/
def OutSupported (D : SeqData) (Θ : ThinFam) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ T : LStr D.Pl D.K (D.level n),
    ∀ᵐ p ∂(bodyMeasure (cOf (D.level n).ν) (gRate D.Pl) (D.level n).ν),
      (D.level n).Scut D.K < p.1 → ((Θ D n z (thinPart T) : LVel D.Pl (D.level n)) :
        Chart → Merid) p = 0

/-- The assembly: per-bin bound + support + bins-to-norm give the operator bound
`‖Θ (thin T)‖ ≤ C ν^{-k} e^{γ/(10ν)} ‖T‖` (source 5594-5600). -/
theorem thinAt_of_bins (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) (Θ : ThinFam)
    (hP : D.PerBinVelocity Θ) (hS : D.OutSupported Θ) (hT : BinTriangle) :
    ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∀ T : LStr D.Pl D.K (D.level n),
        ‖Θ D n z (thinPart T)‖ ≤ C * (D.level n).ν⁻¹ ^ k *
          Real.exp ((gRate D.Pl / 10) / (D.level n).ν) * ‖T‖ := by
  obtain ⟨C, k, hC⟩ := hP
  have hh : 0 < D.K.hbin := by unfold ReturnConsts.hbin; linarith [hst.δ_pos]
  have hle := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  refine ⟨|C| * binK D.K.hbin, k, ?_⟩
  filter_upwards [hC, hS, hle] with n hCn hSn ⟨hν1, hε1⟩ z hz T
  have hεpos : 0 < (D.level n).ε := (D.level n).ε_pos
  have hνpos : 0 < (D.level n).ν := (D.level n).ν_pos
  set φ := Θ D n z (thinPart T) with hφ
  set M : ℝ := |C| * (D.level n).ν⁻¹ ^ k * Real.exp ((gRate D.Pl / 10) / (D.level n).ν) *
    (D.level n).ε ^ (3 / 2 : ℝ) * ‖T‖ with hM
  have hM0 : 0 ≤ M := by positivity
  have hScut : (D.level n).Scut D.K = (D.level n).ε ^ (-D.K.b) := rfl
  have hS0 : 0 ≤ (D.level n).Scut D.K := by rw [hScut]; positivity
  obtain ⟨hsum, hbd⟩ := binSum_bound ((D.level n).Scut D.K) D.K.hbin M hS0 hh hM0
  have hbins : ∀ j, binNorm (cOf (D.level n).ν) (gRate D.Pl) (D.level n).ν
      ((D.level n).Scut D.K) D.K.hbin j φ ≤
      M * (binUpper ((D.level n).Scut D.K) D.K.hbin j ^ (1 / 2 : ℝ) +
        binUpper ((D.level n).Scut D.K) D.K.hbin j ^ (3 / 4 : ℝ)) := by
    intro j
    refine (hCn z hz T j).trans ?_
    have hs : 0 ≤ binUpper ((D.level n).Scut D.K) D.K.hbin j ^ (1 / 2 : ℝ) +
        binUpper ((D.level n).Scut D.K) D.K.hbin j ^ (3 / 4 : ℝ) := by
      unfold binUpper
      positivity
    have : C * (D.level n).ν⁻¹ ^ k * Real.exp ((gRate D.Pl / 10) / (D.level n).ν) *
        (D.level n).ε ^ (3 / 2 : ℝ) * ‖T‖ ≤ M := by
      rw [hM]
      have : 0 ≤ (D.level n).ν⁻¹ ^ k * Real.exp ((gRate D.Pl / 10) / (D.level n).ν) *
        (D.level n).ε ^ (3 / 2 : ℝ) * ‖T‖ := by positivity
      nlinarith [le_abs_self C]
    calc _ = (C * (D.level n).ν⁻¹ ^ k * Real.exp ((gRate D.Pl / 10) / (D.level n).ν) *
          (D.level n).ε ^ (3 / 2 : ℝ) * ‖T‖) * (_ + _) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right this hs
  have h1 := hT _ _ _ _ _ hh φ (hSn z hz T) _ hsum hbins
  refine h1.trans (hbd.trans ?_)
  -- `M (S^{1/2} r₁ + S^{3/4} r₂) ≤ |C| K_h ν^{-k} e^{..} ‖T‖`
  set r1 := (1 - Real.exp (-(D.K.hbin * (1 / 2))))⁻¹ with hr1
  set r2 := (1 - Real.exp (-(D.K.hbin * (3 / 4))))⁻¹ with hr2
  have hr1' : 0 ≤ r1 := by
    have : Real.exp (-(D.K.hbin * (1 / 2))) < 1 := exp_neg_mul_lt_one hh (by norm_num)
    exact inv_nonneg.2 (by linarith)
  have hr2' : 0 ≤ r2 := by
    have : Real.exp (-(D.K.hbin * (3 / 4))) < 1 := exp_neg_mul_lt_one hh (by norm_num)
    exact inv_nonneg.2 (by linarith)
  have hb1 := hst.b_lt
  have hb0 := hst.b_pos
  have e1 : (D.level n).ε ^ (3 / 2 : ℝ) * ((D.level n).Scut D.K) ^ (1 / 2 : ℝ) ≤ 1 :=
    eps_mul_cut_le_one hεpos hε1 (by linarith)
  have e2 : (D.level n).ε ^ (3 / 2 : ℝ) * ((D.level n).Scut D.K) ^ (3 / 4 : ℝ) ≤ 1 :=
    eps_mul_cut_le_one hεpos hε1 (by linarith)
  have hQ : 0 ≤ |C| * (D.level n).ν⁻¹ ^ k * Real.exp ((gRate D.Pl / 10) / (D.level n).ν) * ‖T‖ := by
    positivity
  set Q := |C| * (D.level n).ν⁻¹ ^ k * Real.exp ((gRate D.Pl / 10) / (D.level n).ν) * ‖T‖ with hQd
  have hMQ : M = Q * (D.level n).ε ^ (3 / 2 : ℝ) := by rw [hM, hQd]; ring
  have hS12 : 0 ≤ ((D.level n).Scut D.K) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hS0 _
  have hS34 : 0 ≤ ((D.level n).Scut D.K) ^ (3 / 4 : ℝ) := Real.rpow_nonneg hS0 _
  have hε32 : 0 ≤ (D.level n).ε ^ (3 / 2 : ℝ) := Real.rpow_nonneg hεpos.le _
  have hfin : M * (((D.level n).Scut D.K) ^ (1 / 2 : ℝ) * r1 +
      ((D.level n).Scut D.K) ^ (3 / 4 : ℝ) * r2) ≤ Q * (r1 + r2) := by
    rw [hMQ]
    have a1 : (D.level n).ε ^ (3 / 2 : ℝ) * (((D.level n).Scut D.K) ^ (1 / 2 : ℝ) * r1) ≤ r1 := by
      calc _ = ((D.level n).ε ^ (3 / 2 : ℝ) * ((D.level n).Scut D.K) ^ (1 / 2 : ℝ)) * r1 := by ring
        _ ≤ 1 * r1 := mul_le_mul_of_nonneg_right e1 hr1'
        _ = r1 := one_mul _
    have a2 : (D.level n).ε ^ (3 / 2 : ℝ) * (((D.level n).Scut D.K) ^ (3 / 4 : ℝ) * r2) ≤ r2 := by
      calc _ = ((D.level n).ε ^ (3 / 2 : ℝ) * ((D.level n).Scut D.K) ^ (3 / 4 : ℝ)) * r2 := by ring
        _ ≤ 1 * r2 := mul_le_mul_of_nonneg_right e2 hr2'
        _ = r2 := one_mul _
    calc Q * (D.level n).ε ^ (3 / 2 : ℝ) * (((D.level n).Scut D.K) ^ (1 / 2 : ℝ) * r1 +
          ((D.level n).Scut D.K) ^ (3 / 4 : ℝ) * r2)
        = Q * ((D.level n).ε ^ (3 / 2 : ℝ) * (((D.level n).Scut D.K) ^ (1 / 2 : ℝ) * r1) +
          (D.level n).ε ^ (3 / 2 : ℝ) * (((D.level n).Scut D.K) ^ (3 / 4 : ℝ) * r2)) := by ring
      _ ≤ Q * (r1 + r2) := mul_le_mul_of_nonneg_left (add_le_add a1 a2) hQ
  have : |C| * binK D.K.hbin * (D.level n).ν⁻¹ ^ k *
      Real.exp ((gRate D.Pl / 10) / (D.level n).ν) * ‖T‖ = Q * (r1 + r2) := by
    rw [hQd, binK]; ring
  rw [this]
  exact hfin

end SeqData

/-! ## 3. The two leaves -/

/-- From the three estimates to `AgeVelWardThinAt` (any `ω_b ≥ 0`; the margin `3m₀/2 > 0`). -/
theorem SeqData.wardThinAt_of_bins (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (hP : D.PerBinVelocity wardThinFam) (hS : D.OutSupported wardThinFam) (hT : BinTriangle)
    {ωb : ℝ} (hω : 0 ≤ ωb) : D.AgeVelWardThinAt ωb := by
  obtain ⟨C, k, h⟩ := SeqData.thinAt_of_bins D hst wardThinFam hP hS hT
  refine ⟨|C|, k, ?_⟩
  filter_upwards [h, (retNu_tendsto D.σ₀ hst.omega_ne).eventually (ge_mem_nhds one_pos)]
    with n hn hν1 z hz T
  have hνp : 0 < (D.level n).ν := (D.level n).ν_pos
  have hE : Real.exp ((gRate D.Pl / 10) / (D.level n).ν) ≤
      Real.exp ((gRate D.Pl / 10 + ωb + 3 * D.K.m0 / 2) / (D.level n).ν) := by
    refine Real.exp_le_exp.2 (div_le_div_of_nonneg_right ?_ hνp.le)
    linarith [hst.m0_pos]
  have hP' : 0 ≤ (D.level n).ν⁻¹ ^ k := by positivity
  exact lift (hn z hz T) le_rfl hP' le_rfl (Real.exp_pos _).le hE (norm_nonneg T)

/-- From the three estimates to `AgeVelSopThinAt`. -/
theorem SeqData.sopThinAt_of_bins (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (hP : D.PerBinVelocity sopThinFam) (hS : D.OutSupported sopThinFam) (hT : BinTriangle)
    {ωb : ℝ} (hω : 0 ≤ ωb) : D.AgeVelSopThinAt ωb := by
  obtain ⟨C, k, h⟩ := SeqData.thinAt_of_bins D hst sopThinFam hP hS hT
  refine ⟨|C|, k, ?_⟩
  filter_upwards [h] with n hn z hz T
  have hνp : 0 < (D.level n).ν := (D.level n).ν_pos
  have hE : Real.exp ((gRate D.Pl / 10) / (D.level n).ν) ≤
      Real.exp ((gRate D.Pl / 10 + ωb + 3 * D.K.m0 / 2) / (D.level n).ν) := by
    refine Real.exp_le_exp.2 (div_le_div_of_nonneg_right ?_ hνp.le)
    linarith [hst.m0_pos]
  have hP' : 0 ≤ (D.level n).ν⁻¹ ^ k := by positivity
  exact lift (hn z hz T) le_rfl hP' le_rfl (Real.exp_pos _).le hE (norm_nonneg T)

/-- **Leaf (c2) from the bin estimates** (`k₀ = 0`: `ε^{3/2}S^{3/4} ≤ 1` since `b < 1`). -/
theorem ageVelWardThin_of_bins (Pl : PlanarData) (σ₀ mZ dm dp : ℝ)
    (hP : ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ → D.RepairStanding dm dp →
      D.PerBinVelocity wardThinFam)
    (hS : ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ → D.RepairStanding dm dp →
      D.OutSupported wardThinFam)
    (hT : BinTriangle) : AgeVelWardThin Pl σ₀ mZ dm dp := by
  refine ⟨0, fun D hPl hσ hmZ hst => ?_⟩
  refine D.wardThinAt_of_bins hst (hP D hPl hσ hmZ hst) (hS D hPl hσ hmZ hst) hT ?_
  have := hst.b_pos.le
  have := hst.gamma_pos.le
  simp only [Nat.cast_zero, zero_mul]
  exact le_rfl

/-- **Leaf (c1) from the bin estimates.** -/
theorem ageVelSopThin_of_bins (Pl : PlanarData) (σ₀ mZ dm dp : ℝ)
    (hP : ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ → D.RepairStanding dm dp →
      D.PerBinVelocity sopThinFam)
    (hS : ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ → D.RepairStanding dm dp →
      D.OutSupported sopThinFam)
    (hT : BinTriangle) : AgeVelSopThin Pl σ₀ mZ dm dp := by
  refine ⟨0, fun D hPl hσ hmZ hst => ?_⟩
  refine D.sopThinAt_of_bins hst (hP D hPl hσ hmZ hst) (hS D hPl hσ hmZ hst) hT ?_
  simp only [Nat.cast_zero, zero_mul]
  exact le_rfl

end UnforcedLeray.Short.PartIIIb.Concrete

end
