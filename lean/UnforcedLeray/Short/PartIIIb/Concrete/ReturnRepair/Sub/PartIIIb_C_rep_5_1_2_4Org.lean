import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2Org

/-!
# `PartIII-b:C/rep/5/1/2/4/org`: the stream transition `Y` on thin sources, bin by bin

Source `the November 2 reference manuscript` 5569-5605.

## Correction of the per-bin statement of `…_5_1_2Org`

`SeqData.PerBinVelocity` of `PartIII-b_C_rep_5_1_2Org.lean` carries the factor `ε^{3/2}` **and** the
gain growth `e^{γ/(10ν)}`.  In the source (5585-5605) the factor `ε^{3/2}` is part of the margin:
the ungained bin velocity is `C ε^{3/2}(s_j^{1/2}+s_j^{3/4})‖T‖_{Z₁}`, and the gain bookkeeping
`3d₀/2 - γ + 4γ/9 = -γ/18`, `3d₀/2 - 3γ/5 = -γ/10` (with `ε = e^{-d₀/ν}P_ν`, `d₀ = γ/3`) is the
statement that `ε^{3/2}·g(source)/g(output) ≤ e^{γ/(10ν)}`.  So the gained bin velocity is
`C ν^{-k} e^{γ/(10ν)}(s_j^{1/2}+s_j^{3/4})‖T‖`, **without** the extra `ε^{3/2}` (the sibling
`GainMarginAt` of `…_5_1_1Org` has exactly this form).  The extra factor in `PerBinVelocity` makes it
stronger than the source by `e^{γ/(2ν)}` (for a source at age `1.5/ν` and an output at age `≪ 1/ν`
the gain ratio alone is `e^{3γ/(5ν)}` against the claimed `e^{γ/(10ν)}`), so it is not provable.
The sum over the bins then produces `S^{3/4} = ε^{-3b/4}`, absorbed by `ω_b = k₀ b γ/3` with `k₀ = 1`
(`ε^{-1} = e^{γ/(3ν)}P_ν`), exactly as in the source ("up to a fixed polynomial in `S`", "Put
`ω_b = k b d₀`").

**Further correction (organizer `PartIII-b:C/rep/5/1/cancel/org`).**  `PerBinVelocityG wardThinFam` is itself
false for the early output bins (`WardGainMarginFalse.lean`); the generic `PerBinVelocityG`,
`thinAtG_of_bins` are used with the family `ageThinFam = sopThinFam + wardThinFam`
(`PartIII-b_C_rep_5_1_cancelOrg.lean`), and `wardThinAtG_of_bins`, `ageVelWardThin_ofG` below are
kept as unused implications.

This file proves, with the corrected statement:

* `PerBinVelocityG` (gained bin bound, no `ε^{3/2}`), `ScutPowBound` (`S^{3/4} ≤ P_ν e^{ω_b/ν}`);
* `thinAtG_of_bins` (bin sum), `wardThinAtG_of_bins`, `ageVelWardThin_ofG` (the leaf `AgeVelWardThin`,
  `k₀ = 1`), from `PerBinVelocityG`, `OutSupported`, `BinTriangle`, `ScutPowBound`.

and states, over the real objects `wardOps`, `wardY`, `chiOStr`, `thinPart`, `bodyMeasure`,
`ReturnLevel.Scut`, the Props from which `PerBinVelocityG wardThinFam` is assembled
(`WardYBinMassAt` kernel bound, `ChiOThinRep`, `BinNormToAge`, `MassGained`, `WardGainMarginG`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace SeqData

/-! ## 1. The corrected per-bin statement and the bin sum -/

/-- **Gained per-bin velocity** (source 5585-5605, corrected): on each output bin `j` (upper age
`s_j = S e^{-hj}`, `S = ε^{-b}`, `h = δ/4`) the thin velocity of `Θ` is at most
`C ν^{-k} e^{γ/(10ν)}(s_j^{1/2}+s_j^{3/4})‖T‖` in the gained norms (the factor `ε^{3/2}` of the
kernel estimate is inside the margin `e^{γ/(10ν)}`). -/
def PerBinVelocityG (D : SeqData) (Θ : ThinFam) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ∀ T : LStr D.Pl D.K (D.level n), ∀ j : ℕ,
      binNorm (cOf (D.level n).ν) (gRate D.Pl) (D.level n).ν ((D.level n).Scut D.K)
          D.K.hbin j (Θ D n z (thinPart T)) ≤
        C * (D.level n).ν⁻¹ ^ k * Real.exp ((gRate D.Pl / 10) / (D.level n).ν) *
          (binUpper ((D.level n).Scut D.K) D.K.hbin j ^ (1 / 2 : ℝ) +
            binUpper ((D.level n).Scut D.K) D.K.hbin j ^ (3 / 4 : ℝ)) * ‖T‖

/-- **The output cut is a polynomial times the `ω_b` growth** (source 5594-5600 "up to a fixed
polynomial in `S`", "`ω_b = k b d₀`"): `S^{3/4} = ε^{-3b/4} ≤ C ν^{-k} e^{(b γ/3)/ν}`, from
`ε³ = e^{-γ/ν}ν^{Re κ-5-2σ₀}/(2|𝒞(σ₀)|)` (`retEps`) and `b < 1`... (`d₀ = γ/3`). -/
def ScutPowBound (D : SeqData) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop,
    ((D.level n).Scut D.K) ^ (3 / 4 : ℝ) ≤
      C * (D.level n).ν⁻¹ ^ k * Real.exp ((D.K.b * (gRate D.Pl / 3)) / (D.level n).ν)

/-- The assembly with the corrected per-bin bound: per-bin bound + support + bins-to-norm +
`ScutPowBound` give `‖Θ(thin T)‖ ≤ C ν^{-k} e^{(γ/10 + bγ/3)/ν}‖T‖` (source 5594-5600). -/
theorem thinAtG_of_bins (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) (Θ : ThinFam)
    (hP : D.PerBinVelocityG Θ) (hS : D.OutSupported Θ) (hT : BinTriangle)
    (hSc : D.ScutPowBound) :
    ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∀ T : LStr D.Pl D.K (D.level n),
        ‖Θ D n z (thinPart T)‖ ≤ C * (D.level n).ν⁻¹ ^ k *
          Real.exp ((gRate D.Pl / 10 + D.K.b * (gRate D.Pl / 3)) / (D.level n).ν) * ‖T‖ := by
  obtain ⟨C, k, hC⟩ := hP
  obtain ⟨C', k', hC'⟩ := hSc
  have hh : 0 < D.K.hbin := by unfold ReturnConsts.hbin; linarith [hst.δ_pos]
  have hle := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  refine ⟨|C| * binK D.K.hbin * |C'|, k + k', ?_⟩
  filter_upwards [hC, hS, hle, hC'] with n hCn hSn ⟨hν1, hε1⟩ hC'n z hz T
  have hεpos : 0 < (D.level n).ε := (D.level n).ε_pos
  have hνpos : 0 < (D.level n).ν := (D.level n).ν_pos
  set φ := Θ D n z (thinPart T) with hφ
  set M : ℝ := |C| * (D.level n).ν⁻¹ ^ k * Real.exp ((gRate D.Pl / 10) / (D.level n).ν) * ‖T‖
    with hM
  have hM0 : 0 ≤ M := by positivity
  have hScut : (D.level n).Scut D.K = (D.level n).ε ^ (-D.K.b) := rfl
  have hS0 : 0 ≤ (D.level n).Scut D.K := by rw [hScut]; positivity
  have hS1 : 1 ≤ (D.level n).Scut D.K := by
    rw [hScut]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hεpos hε1 (by linarith [hst.b_pos])
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
    have : C * (D.level n).ν⁻¹ ^ k * Real.exp ((gRate D.Pl / 10) / (D.level n).ν) * ‖T‖ ≤ M := by
      rw [hM]
      have : 0 ≤ (D.level n).ν⁻¹ ^ k * Real.exp ((gRate D.Pl / 10) / (D.level n).ν) * ‖T‖ := by
        positivity
      nlinarith [le_abs_self C]
    calc _ = (C * (D.level n).ν⁻¹ ^ k * Real.exp ((gRate D.Pl / 10) / (D.level n).ν) * ‖T‖) *
          (_ + _) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right this hs
  have h1 := hT _ _ _ _ _ hh φ (hSn z hz T) _ hsum hbins
  refine h1.trans (hbd.trans ?_)
  set r1 := (1 - Real.exp (-(D.K.hbin * (1 / 2))))⁻¹ with hr1
  set r2 := (1 - Real.exp (-(D.K.hbin * (3 / 4))))⁻¹ with hr2
  have hr1' : 0 ≤ r1 := by
    have : Real.exp (-(D.K.hbin * (1 / 2))) < 1 := exp_neg_mul_lt_one hh (by norm_num)
    exact inv_nonneg.2 (by linarith)
  have hr2' : 0 ≤ r2 := by
    have : Real.exp (-(D.K.hbin * (3 / 4))) < 1 := exp_neg_mul_lt_one hh (by norm_num)
    exact inv_nonneg.2 (by linarith)
  set S := (D.level n).Scut D.K with hSdef
  have hS12 : S ^ (1 / 2 : ℝ) ≤ S ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hS1 (by norm_num)
  have hS34 : 0 ≤ S ^ (3 / 4 : ℝ) := Real.rpow_nonneg hS0 _
  have hpow : S ^ (3 / 4 : ℝ) ≤ |C'| * (D.level n).ν⁻¹ ^ k' *
      Real.exp ((D.K.b * (gRate D.Pl / 3)) / (D.level n).ν) := by
    refine hC'n.trans ?_
    have : 0 ≤ (D.level n).ν⁻¹ ^ k' * Real.exp ((D.K.b * (gRate D.Pl / 3)) / (D.level n).ν) := by
      positivity
    nlinarith [le_abs_self C']
  have hA : S ^ (1 / 2 : ℝ) * r1 + S ^ (3 / 4 : ℝ) * r2 ≤ S ^ (3 / 4 : ℝ) * (r1 + r2) := by
    nlinarith [mul_le_mul_of_nonneg_right hS12 hr1']
  have hexp : Real.exp ((gRate D.Pl / 10 + D.K.b * (gRate D.Pl / 3)) / (D.level n).ν) =
      Real.exp ((gRate D.Pl / 10) / (D.level n).ν) *
        Real.exp ((D.K.b * (gRate D.Pl / 3)) / (D.level n).ν) := by
    rw [← Real.exp_add, add_div]
  have hpk : (D.level n).ν⁻¹ ^ (k + k') = (D.level n).ν⁻¹ ^ k * (D.level n).ν⁻¹ ^ k' := pow_add _ _ _
  have hE1 : 0 ≤ Real.exp ((gRate D.Pl / 10) / (D.level n).ν) := (Real.exp_pos _).le
  have hQ : 0 ≤ (r1 + r2) := add_nonneg hr1' hr2'
  calc M * (S ^ (1 / 2 : ℝ) * r1 + S ^ (3 / 4 : ℝ) * r2)
      ≤ M * (S ^ (3 / 4 : ℝ) * (r1 + r2)) := mul_le_mul_of_nonneg_left hA hM0
    _ ≤ M * ((|C'| * (D.level n).ν⁻¹ ^ k' *
          Real.exp ((D.K.b * (gRate D.Pl / 3)) / (D.level n).ν)) * (r1 + r2)) := by
        gcongr
    _ = |C| * binK D.K.hbin * |C'| * (D.level n).ν⁻¹ ^ (k + k') *
          Real.exp ((gRate D.Pl / 10 + D.K.b * (gRate D.Pl / 3)) / (D.level n).ν) * ‖T‖ := by
        rw [hM, hpk, hexp, binK]; ring

/-- From the bin estimates to `AgeVelWardThinAt` with `ω_b = b γ/3` (the margin `3m₀/2 > 0`). -/
theorem wardThinAtG_of_bins (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (hP : D.PerBinVelocityG wardThinFam) (hS : D.OutSupported wardThinFam) (hT : BinTriangle)
    (hSc : D.ScutPowBound) : D.AgeVelWardThinAt (D.K.b * (gRate D.Pl / 3)) := by
  obtain ⟨C, k, h⟩ := SeqData.thinAtG_of_bins D hst wardThinFam hP hS hT hSc
  refine ⟨|C|, k, ?_⟩
  filter_upwards [h, (retNu_tendsto D.σ₀ hst.omega_ne).eventually (ge_mem_nhds one_pos)]
    with n hn hν1 z hz T
  have hνp : 0 < (D.level n).ν := (D.level n).ν_pos
  have hE : Real.exp ((gRate D.Pl / 10 + D.K.b * (gRate D.Pl / 3)) / (D.level n).ν) ≤
      Real.exp ((gRate D.Pl / 10 + D.K.b * (gRate D.Pl / 3) + 3 * D.K.m0 / 2) /
        (D.level n).ν) := by
    refine Real.exp_le_exp.2 (div_le_div_of_nonneg_right ?_ hνp.le)
    linarith [hst.m0_pos]
  have hP' : 0 ≤ (D.level n).ν⁻¹ ^ k := by positivity
  exact lift (hn z hz T) le_rfl hP' le_rfl (Real.exp_pos _).le hE (norm_nonneg T)

end SeqData

/-- **Leaf (c2) from the corrected bin estimates** (`k₀ = 1`, `ω_b = b γ/3`). -/
theorem ageVelWardThin_ofG (Pl : PlanarData) (σ₀ mZ dm dp : ℝ)
    (hP : ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ → D.RepairStanding dm dp →
      D.PerBinVelocityG wardThinFam)
    (hS : ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ → D.RepairStanding dm dp →
      D.OutSupported wardThinFam)
    (hSc : ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ → D.RepairStanding dm dp →
      D.ScutPowBound)
    (hT : BinTriangle) : AgeVelWardThin Pl σ₀ mZ dm dp := by
  refine ⟨1, fun D hPl hσ hmZ hst => ?_⟩
  have := D.wardThinAtG_of_bins hst (hP D hPl hσ hmZ hst) (hS D hPl hσ hmZ hst) hT
    (hSc D hPl hσ hmZ hst)
  simpa using this

end UnforcedLeray.Short.PartIIIb.Concrete

end
