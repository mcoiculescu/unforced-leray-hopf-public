import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4.WardBin
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4.WardGainMarginFalse

/-!
# Assembly of the gained per-bin velocity of `Y` on thin sources, late output bins

Source `the November 2 reference manuscript` 5585-5605.  From the Props of
`WardBin.lean` (kernel bound, `χ_o`-representative, gained-to-ungained bin norm, gained thin mass)
the late-output margin `LateGainMarginG` (`WardGainMarginFalse.lean`) and the Ward pin `IsWardTriple`
of `wardOps` (from `RegimePins.ward`): `D.WardLateBin`, the gained per-bin velocity of `Y` on the
bins with `ν s_{j+1} ≥ 2/3`.  (The former statement for all bins, `PerBinVelocityG wardThinFam`, is
false: for early output bins `Y` alone grows like `e^{γ/(6ν)}`; see `WardGainMarginFalse.lean`.  The
source bounds `Y` only through the sum `S_far T + Y[T]`, 5688-5689.)
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gainG_pos' (γ ν s : ℝ) : 0 < UnforcedLeray.Short.IIIa.gainG γ ν s := Real.exp_pos _

/-- The ENNReal chain of one bin, as a real inequality. -/
theorem chain_core {b r A A' B B' t : ℝ} {ag mass : ℝ≥0∞} (hr : 0 ≤ r) (hA' : 0 ≤ A')
    (hB' : 0 ≤ B') (ht : 0 ≤ t) (hAA : A ≤ A') (hBB : B ≤ B')
    (h1 : ENNReal.ofReal b ≤ ENNReal.ofReal r * ag)
    (h2 : ag ≤ ENNReal.ofReal A * mass)
    (h3 : mass ≤ ENNReal.ofReal B * ENNReal.ofReal t) : b ≤ r * A' * B' * t := by
  have h4 : ENNReal.ofReal b ≤ ENNReal.ofReal r * (ENNReal.ofReal A' *
      (ENNReal.ofReal B' * ENNReal.ofReal t)) := by
    refine h1.trans ?_
    have h6 : ag ≤ ENNReal.ofReal A' * (ENNReal.ofReal B' * ENNReal.ofReal t) :=
      h2.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hAA)
        (h3.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hBB) le_rfl)))
    exact mul_le_mul' le_rfl h6
  have h5 : ENNReal.ofReal r * (ENNReal.ofReal A' * (ENNReal.ofReal B' * ENNReal.ofReal t)) =
      ENNReal.ofReal (r * A' * B' * t) := by
    rw [← ENNReal.ofReal_mul hB', ← ENNReal.ofReal_mul hA', ← ENNReal.ofReal_mul hr]
    ring_nf
  rw [h5] at h4
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h4

/-- The real arithmetic of one bin. -/
theorem real_core {sq G CK C0 CG P1 P2 P3 X s5 B0 E W Sg gn t : ℝ} (hsq : 0 ≤ sq)
    (hG : G = gn⁻¹) (hgn : 0 < gn) (hX : 0 ≤ X) (hE : 0 ≤ E) (hW : 0 ≤ W) (hP1 : 0 ≤ P1)
    (hP2 : 0 ≤ P2) (hP3 : 0 ≤ P3) (hB0 : 0 ≤ B0) (hs5 : 0 ≤ s5) (ht : 0 ≤ t)
    (hmargin : X * E ≤ CG * P3 * W * gn) (harith : s5 * B0 ≤ Sg) :
    sq * G * (|CK| * P1 * X * s5) * (|C0| * P2 * B0 * E) * t ≤
      (sq * |CK| * |C0| * |CG|) * (P1 * P2 * P3) * W * Sg * t := by
  have hG0 : 0 ≤ G := by rw [hG]; exact inv_nonneg.2 hgn.le
  have hm : G * (X * E) ≤ |CG| * P3 * W := by
    have h1 : G * (X * E) ≤ G * (CG * P3 * W * gn) := mul_le_mul_of_nonneg_left hmargin hG0
    have h2 : G * (CG * P3 * W * gn) = CG * P3 * W := by
      rw [hG]; field_simp
    have h3 : CG * P3 * W ≤ |CG| * P3 * W := by
      have : 0 ≤ P3 * W := mul_nonneg hP3 hW
      nlinarith [le_abs_self CG]
    linarith
  have hS0 : 0 ≤ s5 * B0 := mul_nonneg hs5 hB0
  have hSg : 0 ≤ Sg := hS0.trans harith
  have e : sq * G * (|CK| * P1 * X * s5) * (|C0| * P2 * B0 * E) * t =
      (sq * |CK| * |C0| * (P1 * P2)) * (G * (X * E)) * (s5 * B0) * t := by ring
  rw [e]
  have e2 : (sq * |CK| * |C0| * |CG|) * (P1 * P2 * P3) * W * Sg * t =
      (sq * |CK| * |C0| * (P1 * P2)) * (|CG| * P3 * W) * Sg * t := by ring
  rw [e2]
  have h0 : 0 ≤ sq * |CK| * |C0| * (P1 * P2) := by positivity
  have hq : 0 ≤ G * (X * E) := by positivity
  gcongr

/-- **Late-bin gained velocity of `Y`** (5585-5605): on the output bins `j` with
`ν s_{j+1} ≥ 2/3` (late output, margin `-γ/18` at the source threshold `4/5`), the gained bin norm
of `Y(thinPart T)` is at most `C ν^{-k} e^{γ/(10ν)}(s_j^{1/2}+s_j^{3/4})‖T‖`. -/
def SeqData.WardLateBin (D : SeqData) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ∀ T : LStr D.Pl D.K (D.level n), ∀ j : ℕ,
      2 / 3 ≤ (D.level n).ν * binUpper ((D.level n).Scut D.K) D.K.hbin (j + 1) →
      binNorm (cOf (D.level n).ν) (gRate D.Pl) (D.level n).ν ((D.level n).Scut D.K)
          D.K.hbin j (wardThinFam D n z (thinPart T)) ≤
        C * (D.level n).ν⁻¹ ^ k * Real.exp ((gRate D.Pl / 10) / (D.level n).ν) *
          (binUpper ((D.level n).Scut D.K) D.K.hbin j ^ (1 / 2 : ℝ) +
            binUpper ((D.level n).Scut D.K) D.K.hbin j ^ (3 / 4 : ℝ)) * ‖T‖

theorem wardLateBin_of (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (hTM : ThinMassBound D.K.mZ) (hK : D.WardYBinMassSeq dm dp) (hχ : ChiOThinRep)
    (hBN : BinNormToAge) (hMG : MassGained D.K.mZ) (hGM : D.LateGainMarginG) :
    D.WardLateBin := by
  obtain ⟨CK, kK, hKn⟩ := hK hst
  obtain ⟨C0, k0, hM⟩ := hMG hTM
  obtain ⟨CG, kG, hGn⟩ := hGM
  have hle := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  refine ⟨Real.sqrt Real.pi * |CK| * |C0| * |CG|, kK + 2 * k0 + kG, ?_⟩
  filter_upwards [hKn, hGn, hle, hst.pins] with n hKn hGn ⟨hν1, hε1⟩ hpins z hz T j hj
  have hνpos : 0 < (D.level n).ν := (D.level n).ν_pos
  have hεpos : 0 < (D.level n).ε := (D.level n).ε_pos
  have hν1' : (D.level n).ν ≤ 1 := hν1
  have hW : IsWardTriple (wardOps D.Pl D.K (D.level n) (D.mu n z)).1
      (wardOps D.Pl D.K (D.level n) (D.mu n z)).2.1
      (wardOps D.Pl D.K (D.level n) (D.mu n z)).2.2 (D.level n).ε (D.mu n z) D.K.hχo D.K.χy
      (D.level n).U (D.level n).pres := Classical.epsilon_spec (hpins z hz).ward
  obtain ⟨g, gm, gz, g1, g2, gle⟩ := hχ (cOf (D.level n).ν) D.K.mZ ((D.level n).ρb D.Pl D.K)
    (gRate D.Pl) (D.level n).ν D.K.hχo hνpos T
  have hY := (hW (thinPart T) g 0 g1 g2).1
  rw [add_zero] at hY
  have hScut : (D.level n).Scut D.K = (D.level n).ε ^ (-D.K.b) := rfl
  have hS0 : 0 < (D.level n).Scut D.K := by rw [hScut]; positivity
  have hs0 : 0 < binUpper ((D.level n).Scut D.K) D.K.hbin j := by unfold binUpper; positivity
  have hu0 : 0 ≤ binUpper ((D.level n).Scut D.K) D.K.hbin (j + 1) := by unfold binUpper; positivity
  have hδp : 0 < D.K.δ := hst.δ_pos
  have hγ : 0 ≤ gRate D.Pl := hst.gamma_pos.le
  have hgn : 0 < UnforcedLeray.Short.IIIa.gainG (gRate D.Pl) (D.level n).ν
      (binUpper ((D.level n).Scut D.K) D.K.hbin (j + 1)) := gainG_pos' _ _ _
  have hG0 : 0 ≤ (UnforcedLeray.Short.IIIa.gainG (gRate D.Pl) (D.level n).ν
      (binUpper ((D.level n).Scut D.K) D.K.hbin (j + 1)))⁻¹ := inv_nonneg.2 hgn.le
  have hginv : ∀ p ∈ binSet ((D.level n).Scut D.K) D.K.hbin j,
      ginv (gRate D.Pl) (D.level n).ν p ≤ (UnforcedLeray.Short.IIIa.gainG (gRate D.Pl)
        (D.level n).ν (binUpper ((D.level n).Scut D.K) D.K.hbin (j + 1)))⁻¹ := by
    intro p hp
    have hup : binUpper ((D.level n).Scut D.K) D.K.hbin (j + 1) < p.1 := hp.1
    unfold ginv
    refine inv_anti₀ hgn ?_
    exact gainG_mono hγ hνpos hu0 (le_max_of_le_left hup.le)
  have hc1 : 1 ≤ cOf (D.level n).ν := by
    unfold cOf
    have : (D.level n).ν ^ 2 ≤ 1 := by nlinarith
    exact (one_le_inv₀ (by positivity)).2 this
  have h1 := hBN (cOf (D.level n).ν) (gRate D.Pl) (D.level n).ν ((D.level n).Scut D.K)
    D.K.hbin j ((wardOps D.Pl D.K (D.level n) (D.mu n z)).1 (thinPart T)) _ _ hY hG0 hginv
  have h2 := hKn z hz hst.δ_lt j g gm gz
  have hexp1 : 1 ≤ Real.exp (D.K.δ - D.K.hbin) := Real.one_le_exp (by
    unfold ReturnConsts.hbin; linarith)
  have ha : binUpper ((D.level n).Scut D.K) D.K.hbin j ≤
      Real.exp (D.K.δ - D.K.hbin) * binUpper ((D.level n).Scut D.K) D.K.hbin j := by
    nlinarith
  have ha0 := lt_of_lt_of_le hs0 ha
  have h3 := hM (cOf (D.level n).ν) ((D.level n).ρb D.Pl D.K) (gRate D.Pl) (D.level n).ν hc1 hγ
    hνpos T _ ha0 g gle
  rw [← ofReal_norm] at h3
  have hcP : cOf (D.level n).ν ^ k0 = (D.level n).ν⁻¹ ^ (2 * k0) := by
    rw [pow_mul]; unfold cOf; congr 1; exact (inv_pow _ _).symm
  rw [hcP] at h3
  have hX : 0 ≤ (D.level n).ε ^ (3 / 2 : ℝ) := Real.rpow_nonneg hεpos.le _
  have hP1 : 0 ≤ (D.level n).ν⁻¹ ^ kK := by positivity
  have hP2 : 0 ≤ (D.level n).ν⁻¹ ^ (2 * k0) := by positivity
  have hP3 : 0 ≤ (D.level n).ν⁻¹ ^ kG := by positivity
  have hs5 : 0 ≤ binUpper ((D.level n).Scut D.K) D.K.hbin j ^ (5 / 4 : ℝ) :=
    Real.rpow_nonneg hs0.le _
  have hB0 : 0 ≤ (Real.exp (D.K.δ - D.K.hbin) * binUpper ((D.level n).Scut D.K) D.K.hbin j) ^
      (-(3 / 4 : ℝ)) + (Real.exp (D.K.δ - D.K.hbin) *
        binUpper ((D.level n).Scut D.K) D.K.hbin j) ^ (-(1 / 2 : ℝ)) := by positivity
  have hE : 0 ≤ Real.exp (gRate D.Pl / (D.level n).ν) := (Real.exp_pos _).le
  have hW0 : 0 ≤ Real.exp ((gRate D.Pl / 10) / (D.level n).ν) := (Real.exp_pos _).le
  have key := chain_core (hr := mul_nonneg (Real.sqrt_nonneg _) hG0)
    (A' := |CK| * (D.level n).ν⁻¹ ^ kK * (D.level n).ε ^ (3 / 2 : ℝ) *
      binUpper ((D.level n).Scut D.K) D.K.hbin j ^ (5 / 4 : ℝ))
    (B' := |C0| * (D.level n).ν⁻¹ ^ (2 * k0) * ((Real.exp (D.K.δ - D.K.hbin) *
        binUpper ((D.level n).Scut D.K) D.K.hbin j) ^ (-(3 / 4 : ℝ)) +
        (Real.exp (D.K.δ - D.K.hbin) * binUpper ((D.level n).Scut D.K) D.K.hbin j) ^
          (-(1 / 2 : ℝ))) * Real.exp (gRate D.Pl / (D.level n).ν))
    (by positivity) (by positivity) (norm_nonneg T)
    (by
      have : 0 ≤ (D.level n).ν⁻¹ ^ kK * (D.level n).ε ^ (3 / 2 : ℝ) *
          binUpper ((D.level n).Scut D.K) D.K.hbin j ^ (5 / 4 : ℝ) := by positivity
      nlinarith [le_abs_self CK])
    (by
      have : 0 ≤ (D.level n).ν⁻¹ ^ (2 * k0) * ((Real.exp (D.K.δ - D.K.hbin) *
        binUpper ((D.level n).Scut D.K) D.K.hbin j) ^ (-(3 / 4 : ℝ)) +
        (Real.exp (D.K.δ - D.K.hbin) * binUpper ((D.level n).Scut D.K) D.K.hbin j) ^
          (-(1 / 2 : ℝ))) * Real.exp (gRate D.Pl / (D.level n).ν) := by positivity
      nlinarith [le_abs_self C0])
    h1 h2 h3
  refine key.trans ?_
  have hr := real_core (sq := Real.sqrt Real.pi) (CK := CK) (C0 := C0) (CG := CG)
    (G := (UnforcedLeray.Short.IIIa.gainG (gRate D.Pl) (D.level n).ν
      (binUpper ((D.level n).Scut D.K) D.K.hbin (j + 1)))⁻¹)
    (gn := UnforcedLeray.Short.IIIa.gainG (gRate D.Pl) (D.level n).ν
      (binUpper ((D.level n).Scut D.K) D.K.hbin (j + 1)))
    (P1 := (D.level n).ν⁻¹ ^ kK) (P2 := (D.level n).ν⁻¹ ^ (2 * k0)) (P3 := (D.level n).ν⁻¹ ^ kG)
    (X := (D.level n).ε ^ (3 / 2 : ℝ)) (s5 := binUpper ((D.level n).Scut D.K) D.K.hbin j ^ (5 / 4 : ℝ))
    (B0 := (Real.exp (D.K.δ - D.K.hbin) * binUpper ((D.level n).Scut D.K) D.K.hbin j) ^
      (-(3 / 4 : ℝ)) + (Real.exp (D.K.δ - D.K.hbin) *
        binUpper ((D.level n).Scut D.K) D.K.hbin j) ^ (-(1 / 2 : ℝ)))
    (E := Real.exp (gRate D.Pl / (D.level n).ν))
    (W := Real.exp ((gRate D.Pl / 10) / (D.level n).ν))
    (Sg := binUpper ((D.level n).Scut D.K) D.K.hbin j ^ (1 / 2 : ℝ) +
      binUpper ((D.level n).Scut D.K) D.K.hbin j ^ (3 / 4 : ℝ)) (t := ‖T‖)
    (Real.sqrt_nonneg _) rfl hgn hX hE hW0 hP1 hP2 hP3 hB0 hs5 (norm_nonneg T)
    (hGn _ hj) (wardBin_arith hs0 ha)
  have ep : (D.level n).ν⁻¹ ^ (kK + 2 * k0 + kG) =
      (D.level n).ν⁻¹ ^ kK * (D.level n).ν⁻¹ ^ (2 * k0) * (D.level n).ν⁻¹ ^ kG := by
    rw [pow_add, pow_add]
  rw [ep]
  exact hr

end UnforcedLeray.Short.PartIIIb.Concrete

end
