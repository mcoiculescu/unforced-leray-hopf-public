import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_cancel.Assemble

/-!
# The far mask on late bins and on the plateau (early source)

Source `the November 2 reference manuscript` 5585-5599, 5303-5316.  From the true
single-term kernel bound `PerBinVelocityAt` (5585-5593), the gained-to-ungained bin norm
`BinNormToAge`, the ungained `Z_1` norm of the source in the gain norm (`Z1TailGained`,
`EarlyZ1Gained`) and the two gain margins `LateGainMarginG`, `EarlyGainMarginG`:

* `farLateBin_of` : `D.FarLateBin` (late output, source gain `e^{γ/ν}`, output gain `g(s_{j+1})`);
* `farEarlyBin_of` : `D.FarEarlyBin` (plateau, early source gain `g(3/(2ν))`, output gain `≥ 1`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The far mask `S_μ - S_N` of every large level is a `S_far` with the exact kernel
realization (the body of `SopSubIsFarSeq` for one `D`). -/
def SeqData.FarSplit (D : SeqData) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ∃ Sf : LStr D.Pl D.K (D.level n) →L[ℝ] LVel D.Pl (D.level n),
      IsFarMaskG (D.level n).ε⁻¹ (D.mu n z) D.K.δ ((D.level n).Scut D.K) Sf ∧
        Sop D.Pl D.K (D.level n) (D.mu n z) - SNop D.Pl D.K (D.level n) (D.mu n z) = Sf

/-- Uniform constants of the single-term kernel bound `PerBinVelocityAt` (one `D`). -/
def SeqData.KernelBd (D : SeqData) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    PerBinVelocityAt D.Pl D.K (D.level n) (D.mu n z) C k

/-- The geometric facts of a bin at a large level. -/
theorem bin_facts (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) (n : ℕ)
    (hε : 0 < (D.level n).ε) (j : ℕ) :
    0 < binUpper ((D.level n).Scut D.K) D.K.hbin j ∧
      binUpper ((D.level n).Scut D.K) D.K.hbin j ≤ (D.level n).Scut D.K ∧
      0 < D.K.hbin ∧ D.K.hbin < D.K.δ / 2 := by
  have hS : 0 < (D.level n).Scut D.K := by
    have : (D.level n).Scut D.K = (D.level n).ε ^ (-D.K.b) := rfl
    rw [this]; positivity
  have hh : 0 < D.K.hbin := by unfold ReturnConsts.hbin; linarith [hst.δ_pos]
  refine ⟨binUpper_pos hS j, binUpper_le hS.le hh.le j, hh, ?_⟩
  unfold ReturnConsts.hbin; linarith [hst.δ_pos]

theorem farLateBin_of (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (hSF : D.FarSplit) (hK : D.KernelBd) (hBN : BinNormToAge) (hZ : Z1TailGained)
    (hL : D.LateGainMarginG) : D.FarLateBin := by
  obtain ⟨C, k, hC⟩ := hK
  obtain ⟨CL, kL, hLn⟩ := hL
  have hle := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  refine ⟨|C| * |CL|, k + kL, ?_⟩
  filter_upwards [hSF, hC, hLn, hle] with n hsf hKn hLn' ⟨hν1, hε1⟩ z hz T j hj
  have hνp : 0 < (D.level n).ν := (D.level n).ν_pos
  have hεp : 0 < (D.level n).ε := (D.level n).ε_pos
  obtain ⟨Sf, hSf, heq⟩ := hsf z hz
  obtain ⟨hs0, hsS, hh0, hhδ⟩ := bin_facts D hst n hεp j
  have hγ : 0 ≤ gRate D.Pl := hst.gamma_pos.le
  have hsop : sopThinFam D n z (thinPart T) = Sf (thinPart T) := by
    show (Sop D.Pl D.K (D.level n) (D.mu n z) - SNop D.Pl D.K (D.level n) (D.mu n z))
      (thinPart T) = _
    rw [heq]
  rw [hsop]
  have hker := hKn z hz D.K.hbin (binUpper ((D.level n).Scut D.K) D.K.hbin j) hh0 hhδ hs0 hsS
    Sf hSf T
  rw [← binUpper_succ] at hker
  have hu0 : 0 ≤ binUpper ((D.level n).Scut D.K) D.K.hbin (j + 1) :=
    (binUpper_pos (by have := hs0; exact lt_of_lt_of_le hs0 hsS) (j + 1)).le
  have hgn : 0 < UnforcedLeray.Short.IIIa.gainG (gRate D.Pl) (D.level n).ν
      (binUpper ((D.level n).Scut D.K) D.K.hbin (j + 1)) := gainG_pos' _ _ _
  have hG0 : 0 ≤ (UnforcedLeray.Short.IIIa.gainG (gRate D.Pl) (D.level n).ν
      (binUpper ((D.level n).Scut D.K) D.K.hbin (j + 1)))⁻¹ := inv_nonneg.2 hgn.le
  have hS0 : 0 ≤ (D.level n).Scut D.K := (lt_of_lt_of_le hs0 hsS).le
  have h1 := binNorm_le_velBin hBN (cOf (D.level n).ν) (gRate D.Pl) (D.level n).ν
    ((D.level n).Scut D.K) D.K.hbin j (Sf (thinPart T)) _ _ Filter.EventuallyEq.rfl hG0
    (ginv_le_on_bin hγ hνp hS0 hh0.le j)
  have hz1 := hZ (cOf (D.level n).ν) D.K.mZ ((D.level n).ρb D.Pl D.K) (gRate D.Pl)
    (D.level n).ν hγ hνp T (Real.exp (D.K.δ - D.K.hbin) *
      binUpper ((D.level n).Scut D.K) D.K.hbin j)
  rw [← ofReal_norm] at hz1
  set s := binUpper ((D.level n).Scut D.K) D.K.hbin j with hsdef
  set gn := UnforcedLeray.Short.IIIa.gainG (gRate D.Pl) (D.level n).ν
      (binUpper ((D.level n).Scut D.K) D.K.hbin (j + 1)) with hgndef
  set P := (D.level n).ν⁻¹ ^ k with hPdef
  set Sg := s ^ (1 / 2 : ℝ) + s ^ (3 / 4 : ℝ) with hSgdef
  have hSg : 0 ≤ Sg := by positivity
  have hX : 0 ≤ (D.level n).ε ^ (3 / 2 : ℝ) := Real.rpow_nonneg hεp.le _
  have hP0 : 0 ≤ P := by positivity
  have hAA : C * P * (D.level n).ε ^ (3 / 2 : ℝ) * Sg ≤ |C| * P * (D.level n).ε ^ (3 / 2 : ℝ) * Sg := by
    have : 0 ≤ P * (D.level n).ε ^ (3 / 2 : ℝ) * Sg := by positivity
    nlinarith [le_abs_self C]
  have hvb : velBin (cOf (D.level n).ν) (binUpper ((D.level n).Scut D.K) D.K.hbin (j + 1)) s
      (Sf (thinPart T) : Chart → Merid) ≤
      ENNReal.ofReal (|C| * P * (D.level n).ε ^ (3 / 2 : ℝ) * Sg) *
        z1Tail (cOf (D.level n).ν) D.K.mZ (Real.exp (D.K.δ - D.K.hbin) * s)
          (((thinPart T).fst : Lp Ten3 2 _) : Chart → Ten3) :=
    hker.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hAA) le_rfl)
  have hchain := le_of_ofReal_chain (b := binNorm (cOf (D.level n).ν) (gRate D.Pl) (D.level n).ν
    ((D.level n).Scut D.K) D.K.hbin j (Sf (thinPart T))) hG0 (by positivity) (Real.exp_pos _).le
    (norm_nonneg T) h1 hvb hz1
  refine hchain.trans ?_
  have hm := hLn' _ hj
  have hm' : (D.level n).ε ^ (3 / 2 : ℝ) * Real.exp (gRate D.Pl / (D.level n).ν) ≤
      |CL| * (D.level n).ν⁻¹ ^ kL * Real.exp ((gRate D.Pl / 10) / (D.level n).ν) * gn := by
    refine hm.trans ?_
    have : 0 ≤ (D.level n).ν⁻¹ ^ kL * Real.exp ((gRate D.Pl / 10) / (D.level n).ν) * gn := by
      positivity
    nlinarith [le_abs_self CL]
  have key : gn⁻¹ * (|C| * P * (D.level n).ε ^ (3 / 2 : ℝ) * Sg) *
      Real.exp (gRate D.Pl / (D.level n).ν) * ‖T‖ =
      (|C| * P * Sg * ‖T‖) * (gn⁻¹ * ((D.level n).ε ^ (3 / 2 : ℝ) *
        Real.exp (gRate D.Pl / (D.level n).ν))) := by ring
  rw [key]
  have m1 : gn⁻¹ * ((D.level n).ε ^ (3 / 2 : ℝ) * Real.exp (gRate D.Pl / (D.level n).ν)) ≤
      |CL| * (D.level n).ν⁻¹ ^ kL * Real.exp ((gRate D.Pl / 10) / (D.level n).ν) := by
    calc _ ≤ gn⁻¹ * (|CL| * (D.level n).ν⁻¹ ^ kL * Real.exp ((gRate D.Pl / 10) / (D.level n).ν) * gn) :=
          mul_le_mul_of_nonneg_left hm' hG0
      _ = _ := by field_simp
  have hQ : 0 ≤ |C| * P * Sg * ‖T‖ := by positivity
  calc _ ≤ (|C| * P * Sg * ‖T‖) * (|CL| * (D.level n).ν⁻¹ ^ kL *
          Real.exp ((gRate D.Pl / 10) / (D.level n).ν)) := mul_le_mul_of_nonneg_left m1 hQ
    _ = _ := by rw [pow_add]; ring

theorem farEarlyBin_of (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (hSF : D.FarSplit) (hK : D.KernelBd) (hBN : BinNormToAge) (hZ : EarlyZ1Gained)
    (hThin : EarlyPartThin) (hE : D.EarlyGainMarginG) : D.FarEarlyBin := by
  obtain ⟨C, k, hC⟩ := hK
  obtain ⟨CE, kE, hEn⟩ := hE
  have hle := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  refine ⟨|C| * |CE|, k + kE, ?_⟩
  filter_upwards [hSF, hC, hEn, hle] with n hsf hKn hEn' ⟨hν1, hε1⟩ z hz T j hj
  have hνp : 0 < (D.level n).ν := (D.level n).ν_pos
  have hεp : 0 < (D.level n).ε := (D.level n).ε_pos
  obtain ⟨Sf, hSf, heq⟩ := hsf z hz
  obtain ⟨hs0, hsS, hh0, hhδ⟩ := bin_facts D hst n hεp j
  have hγ : 0 ≤ gRate D.Pl := hst.gamma_pos.le
  have hsop : sopThinFam D n z (earlyPart D.Pl D.K (D.level n) T) =
      Sf (earlyPart D.Pl D.K (D.level n) T) := by
    show (Sop D.Pl D.K (D.level n) (D.mu n z) - SNop D.Pl D.K (D.level n) (D.mu n z))
      (earlyPart D.Pl D.K (D.level n) T) = _
    rw [heq]
  rw [hsop]
  have hthin : thinPart (earlyPart D.Pl D.K (D.level n) T) =
      earlyPart D.Pl D.K (D.level n) T :=
    hThin (cOf (D.level n).ν) D.K.mZ ((D.level n).ρb D.Pl D.K) (gRate D.Pl) (D.level n).ν
      D.K.hχo T
  have hker := hKn z hz D.K.hbin (binUpper ((D.level n).Scut D.K) D.K.hbin j) hh0 hhδ hs0 hsS
    Sf hSf (earlyPart D.Pl D.K (D.level n) T)
  rw [← binUpper_succ, hthin] at hker
  have hS0 : 0 ≤ (D.level n).Scut D.K := (lt_of_lt_of_le hs0 hsS).le
  have hG0 : (0 : ℝ) ≤ 1 := zero_le_one
  have h1 := binNorm_le_velBin hBN (cOf (D.level n).ν) (gRate D.Pl) (D.level n).ν
    ((D.level n).Scut D.K) D.K.hbin j (Sf (earlyPart D.Pl D.K (D.level n) T)) _ 1
    Filter.EventuallyEq.rfl hG0 (fun p _ => ginv_le_one hγ hνp.le p)
  have hz1 := hZ (cOf (D.level n).ν) D.K.mZ ((D.level n).ρb D.Pl D.K) (gRate D.Pl)
    (D.level n).ν D.K.hχo hγ hνp T (Real.exp (D.K.δ - D.K.hbin) *
      binUpper ((D.level n).Scut D.K) D.K.hbin j)
  rw [← ofReal_norm] at hz1
  set s := binUpper ((D.level n).Scut D.K) D.K.hbin j with hsdef
  set P := (D.level n).ν⁻¹ ^ k with hPdef
  set Sg := s ^ (1 / 2 : ℝ) + s ^ (3 / 4 : ℝ) with hSgdef
  set ge := UnforcedLeray.Short.IIIa.gainG (gRate D.Pl) (D.level n).ν (3 / (2 * (D.level n).ν))
    with hgedef
  have hSg : 0 ≤ Sg := by positivity
  have hX : 0 ≤ (D.level n).ε ^ (3 / 2 : ℝ) := Real.rpow_nonneg hεp.le _
  have hP0 : 0 ≤ P := by positivity
  have hge0 : 0 ≤ ge := (Real.exp_pos _).le
  have hAA : C * P * (D.level n).ε ^ (3 / 2 : ℝ) * Sg ≤ |C| * P * (D.level n).ε ^ (3 / 2 : ℝ) * Sg := by
    have : 0 ≤ P * (D.level n).ε ^ (3 / 2 : ℝ) * Sg := by positivity
    nlinarith [le_abs_self C]
  have hvb : velBin (cOf (D.level n).ν) (binUpper ((D.level n).Scut D.K) D.K.hbin (j + 1)) s
      (Sf (earlyPart D.Pl D.K (D.level n) T) : Chart → Merid) ≤
      ENNReal.ofReal (|C| * P * (D.level n).ε ^ (3 / 2 : ℝ) * Sg) *
        z1Tail (cOf (D.level n).ν) D.K.mZ (Real.exp (D.K.δ - D.K.hbin) * s)
          ((((earlyPart D.Pl D.K (D.level n) T).fst : Lp Ten3 2 _)) : Chart → Ten3) :=
    hker.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hAA) le_rfl)
  have hchain := le_of_ofReal_chain (b := binNorm (cOf (D.level n).ν) (gRate D.Pl) (D.level n).ν
    ((D.level n).Scut D.K) D.K.hbin j (Sf (earlyPart D.Pl D.K (D.level n) T))) hG0
    (by positivity) hge0 (norm_nonneg T) h1 hvb hz1
  refine hchain.trans ?_
  have ht0 : 0 ≤ 3 / (2 * (D.level n).ν) := by positivity
  have ht1 : (D.level n).ν * (3 / (2 * (D.level n).ν)) ≤ 3 / 2 := by
    exact le_of_eq (by field_simp)
  have hm := hEn' _ ht0 ht1
  have hm' : (D.level n).ε ^ (3 / 2 : ℝ) * ge ≤
      |CE| * (D.level n).ν⁻¹ ^ kE * Real.exp ((gRate D.Pl / 10) / (D.level n).ν) := by
    refine hm.trans ?_
    have : 0 ≤ (D.level n).ν⁻¹ ^ kE * Real.exp ((gRate D.Pl / 10) / (D.level n).ν) := by
      positivity
    nlinarith [le_abs_self CE]
  have key : 1 * (|C| * P * (D.level n).ε ^ (3 / 2 : ℝ) * Sg) * ge * ‖T‖ =
      (|C| * P * Sg * ‖T‖) * ((D.level n).ε ^ (3 / 2 : ℝ) * ge) := by ring
  rw [key]
  have hQ : 0 ≤ |C| * P * Sg * ‖T‖ := by positivity
  calc _ ≤ (|C| * P * Sg * ‖T‖) * (|CE| * (D.level n).ν⁻¹ ^ kE *
          Real.exp ((gRate D.Pl / 10) / (D.level n).ν)) := mul_le_mul_of_nonneg_left hm' hQ
    _ = _ := by rw [pow_add]; ring

end UnforcedLeray.Short.PartIIIb.Concrete

end
