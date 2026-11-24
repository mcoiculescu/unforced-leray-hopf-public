import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_cancel.FarBins
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_5
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Agree

/-!
# `PartIII-b:C/rep/5/1/cancel/org`: `AgeVelThin` through the sum `S_far T + Y[T]`

Source `the November 2 reference manuscript` 5303-5316, 5594-5599, 5688-5689,
4161-4199, 3902-3920, 5569-5593.

## Finding

The source never bounds `S_far = Sop - SNop` or `Y = (wardOps).1` separately in the gain norms.  The
margins `γ/18` (late output) and `γ/10` (early source) of 5594-5599 are for the pieces of the SUM
`S_far T + Y[T] = (1-χ_y)S_far T + χ_y S_far((1-χ_o)T) + (𝒞_y-χ_y)W_μ + [D_{μ+1},𝒞_y]X_0`
(5306-5316, 5688-5689).  On output ages `s ≤ 4/(5ν)` (`χ_y = 1`) one has `Y = W_μ = -S_μ(χ_oT)`
(4171-4199) and every pair (output `s < 1/ν`, source `t ≥ 6/(5ν)`) is in the far mask, so the
young-old rectangle cancels exactly: `Y(thin T) + S_far(χ_o thin T) = 0`.  Alone, each of
`AgeVelSopThin`, `AgeVelWardThin` contains (±) the rectangle, of gained size
`ε^{3/2} g(2/ν) = P_ν e^{γ/(6ν)} > e^{(γ/10+ω_b+3m₀/2)/ν}`; they are not source statements.

## Design (all assemblies proved here or in `PartIII-b_C_rep_5_1_cancel/`)

* `ageThinFam = sopThinFam + wardThinFam` (`Bridge.lean`), `ageThinFam D n z x = ageVel … x`.
* `PerBinVelocityG ageThinFam` from the bins (`Assemble.lean`, `ageThinPerBinG_of`): late bins
  `ν s_{j+1} ≥ 2/3` by `FarLateBin`, `WardLateBin` (triangle inequality); plateau bins
  `ν s_{j+1} < 2/3` (so `ν s_j < (2/3)e^{δ/4} < 4/5`) by `PlateauCancel` and `FarEarlyBin`.
* `FarLateBin`, `FarEarlyBin` from the true single-term kernel bound `PerBinVelocityAt`
  (`…_5_1_1Org.lean`), `BinNormToAge`, `Z1TailGained`, `EarlyZ1Gained`, `EarlyPartThin` and the margins
  `lateGainMarginG`, `earlyGainMarginG` (`FarBins.lean`).
* `WardLateBin` from the kernel bound for `Y` and `lateGainMarginG` (`…_5_1_2_4/Assembly.lean`).
* The output support `OutSupported ageThinFam` (here), `BinTriangle`, `ScutPowBound` (`…_5_1_2_5`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. Sequence-level forms of the pieces -/

/-- Sequence-level `FarLateBin` and `FarEarlyBin`: the far-mask pieces of the sum. -/
def FarBinsSeq (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ → D.RepairStanding dm dp →
    D.FarLateBin ∧ D.FarEarlyBin

/-- Sequence-level `WardLateBin`: the stream-transition piece of the sum. -/
def WardLateBinSeq (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ → D.RepairStanding dm dp → D.WardLateBin

/-- Sequence-level `PlateauCancel`. -/
def PlateauCancelSeq (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ → D.RepairStanding dm dp → D.PlateauCancel

/-- The two true gain margins of the source (5594-5599). -/
def GainMarginsSeq (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ → D.RepairStanding dm dp →
    D.LateGainMarginG ∧ D.EarlyGainMarginG

theorem gainMarginsSeq (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : GainMarginsSeq Pl σ₀ mZ dm dp :=
  fun D _ _ _ hst => ⟨lateGainMarginG D hst, earlyGainMarginG D hst⟩

/-- `SopSubIsFarSeq` read at one `D`. -/
theorem farSplit_of {Pl : PlanarData} {σ₀ mZ dm dp : ℝ} (h : SopSubIsFarSeq Pl σ₀ mZ dm dp)
    (D : SeqData) (hPl : D.Pl = Pl) (hσ : D.σ₀ = σ₀) (hmZ : D.K.mZ = mZ)
    (hst : D.RepairStanding dm dp) : D.FarSplit :=
  h D hPl hσ hmZ hst

/-- The single-term kernel bound `PerBinVelocitySeq` read at one `D`. -/
theorem kernelBd_of {Pl : PlanarData} {σ₀ mZ dm dp : ℝ} (h : PerBinVelocitySeq Pl σ₀ mZ dm dp)
    (D : SeqData) (hPl : D.Pl = Pl) (hσ : D.σ₀ = σ₀) (hmZ : D.K.mZ = mZ)
    (hst : D.RepairStanding dm dp) : D.KernelBd :=
  h D hPl hσ hmZ hst

/-- **The far-mask pieces of the sum** (5585-5599): `FarBinsSeq` from the kernel bound, the split
`Sop - SNop = S_far`, `BinNormToAge`, `Z1TailGained`, `EarlyZ1Gained`, `EarlyPartThin`. -/
theorem farBinsSeq_of (Pl : PlanarData) (σ₀ mZ dm dp : ℝ)
    (hSF : SopSubIsFarSeq Pl σ₀ mZ dm dp) (hK : PerBinVelocitySeq Pl σ₀ mZ dm dp)
    (hBN : BinNormToAge) (hZ : Z1TailGained) (hZe : EarlyZ1Gained) (hThin : EarlyPartThin) :
    FarBinsSeq Pl σ₀ mZ dm dp := by
  intro D hPl hσ hmZ hst
  have hSF' := farSplit_of hSF D hPl hσ hmZ hst
  have hK' := kernelBd_of hK D hPl hσ hmZ hst
  exact ⟨farLateBin_of D hst hSF' hK' hBN hZ (lateGainMarginG D hst),
    farEarlyBin_of D hst hSF' hK' hBN hZe hThin (earlyGainMarginG D hst)⟩

/-! ## 2. The output support of the sum -/

theorem outSupported_sop (D : SeqData) (hSF : D.FarSplit)
    (hV : ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      FarVanishAboveAt D.Pl D.K (D.level n) (D.mu n z)) : D.OutSupported sopThinFam := by
  filter_upwards [hSF, hV] with n hsf hv z hz T
  obtain ⟨Sf, hSf, heq⟩ := hsf z hz
  have h1 := hv z hz Sf hSf (thinPart T)
  have h2 : ∀ᵐ p ∂(bodyMeasure (cOf (D.level n).ν) (gRate D.Pl) (D.level n).ν),
      (D.level n).Scut D.K ≤ p.1 → (Sf (thinPart T) : Chart → Merid) p = 0 := by
    rw [NearInst.ae_bodyMeasure, ← NearInst.ae_srcMeasure]
    exact h1
  have hsop : sopThinFam D n z (thinPart T) = Sf (thinPart T) := by
    show (Sop D.Pl D.K (D.level n) (D.mu n z) - SNop D.Pl D.K (D.level n) (D.mu n z))
      (thinPart T) = _
    rw [heq]
  filter_upwards [h2] with p hp hpS
  rw [hsop]
  exact hp hpS.le

theorem outSupported_age (D : SeqData) (h1 : D.OutSupported sopThinFam)
    (h2 : D.OutSupported wardThinFam) : D.OutSupported ageThinFam := by
  filter_upwards [h1, h2] with n a1 a2 z hz T
  filter_upwards [a1 z hz T, a2 z hz T,
    Lp.coeFn_add (sopThinFam D n z (thinPart T)) (wardThinFam D n z (thinPart T))] with p r1 r2 r3 hp
  show ((sopThinFam D n z (thinPart T) + wardThinFam D n z (thinPart T) : LVel D.Pl (D.level n)) :
    Chart → Merid) p = 0
  rw [r3, Pi.add_apply, r1 hp, r2 hp, add_zero]

/-! ## 3. The leaf `AgeVelThin` -/

/-- **`AgeVelThin` from the pieces of the sum** (`k₀ = 1`, `ω_b = b γ/3`). -/
theorem ageVelThin_of_pieces (Pl : PlanarData) (σ₀ mZ dm dp : ℝ)
    (hFar : FarBinsSeq Pl σ₀ mZ dm dp) (hWard : WardLateBinSeq Pl σ₀ mZ dm dp)
    (hPC : PlateauCancelSeq Pl σ₀ mZ dm dp) (hSF : SopSubIsFarSeq Pl σ₀ mZ dm dp)
    (hV : FarVanishAboveSeq Pl σ₀ mZ dm dp)
    (hWout : ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ → D.RepairStanding dm dp →
      D.OutSupported wardThinFam)
    (hT : BinTriangle) : AgeVelThin Pl σ₀ mZ dm dp := by
  refine ⟨1, fun D hPl hσ hmZ hst => ?_⟩
  have hPer : D.PerBinVelocityG ageThinFam :=
    ageThinPerBinG_of D hst (hFar D hPl hσ hmZ hst).1 (hFar D hPl hσ hmZ hst).2
      (hWard D hPl hσ hmZ hst) (hPC D hPl hσ hmZ hst)
  have hOut : D.OutSupported ageThinFam :=
    outSupported_age D (outSupported_sop D (farSplit_of hSF D hPl hσ hmZ hst)
      (hV D hPl hσ hmZ hst)) (hWout D hPl hσ hmZ hst)
  obtain ⟨C, k, h⟩ := SeqData.thinAtG_of_bins D hst ageThinFam hPer hOut hT (scutPowBound D hst)
  refine ⟨|C|, k, ?_⟩
  filter_upwards [h, (retNu_tendsto D.σ₀ hst.omega_ne).eventually (ge_mem_nhds one_pos)]
    with n hn hν1 z hz T
  have hνp : 0 < (D.level n).ν := (D.level n).ν_pos
  have e1 : ((1 : ℕ) : ℝ) * D.K.b * (gRate D.Pl / 3) = D.K.b * (gRate D.Pl / 3) := by simp
  have hE : Real.exp ((gRate D.Pl / 10 + D.K.b * (gRate D.Pl / 3)) / (D.level n).ν) ≤
      Real.exp ((gRate D.Pl / 10 + ((1 : ℕ) : ℝ) * D.K.b * (gRate D.Pl / 3) +
        3 * D.K.m0 / 2) / (D.level n).ν) := by
    refine Real.exp_le_exp.2 (div_le_div_of_nonneg_right ?_ hνp.le)
    rw [e1]
    linarith [hst.m0_pos]
  have hP' : 0 ≤ (D.level n).ν⁻¹ ^ k := by positivity
  exact lift (hn z hz T) le_rfl hP' le_rfl (Real.exp_pos _).le hE (norm_nonneg T)

end UnforcedLeray.Short.PartIIIb.Concrete

end
