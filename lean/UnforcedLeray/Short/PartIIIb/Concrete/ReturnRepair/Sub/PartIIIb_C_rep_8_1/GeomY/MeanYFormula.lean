import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.MeanShift
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.Pieces
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.N0
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1_org

/-!
# `PartIII-b:C/rep/8/1/1/2/2` (`geomY`): the exact formula for `Y^mt`

Source `shorter-proof-2026-11-02.tex` lines 5380-5387 and 5427-5432.

For a receiver `y` with `cylR y ≥ √ν/ε` the formula is `meanYFormula_of_shift` (from the shifted
dilation identity `meanShiftIdentity`).  For `cylR y < √ν/ε` the stream cutoff vanishes on a
neighbourhood of `y` (`chiYr` is zero on `(-√ν/ε, √ν/ε)`), so every term of the formula is zero.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-- `chiYr` vanishes on `(-√ν/ε, √ν/ε)`: there `(εr)² < ν`, so `χ_y(ν/(εr)²) = 0`. -/
theorem mYF_chiYr_zero (ν ε : ℝ) (χy : ℝ → ℝ) (hχ : IsStreamCutoff χy) (hν : 0 < ν)
    (hε : 0 < ε) {r : ℝ} (hr : |r| < Real.sqrt ν / ε) : chiYr ν ε χy r = 0 := by
  by_cases h0 : r = 0
  · simp [chiYr, h0]
  · have h1 : |r| * ε < Real.sqrt ν := (lt_div_iff₀ hε).1 hr
    have h2 : (ε * r) ^ 2 = (|r| * ε) ^ 2 := by
      rw [mul_pow, mul_pow, sq_abs]
      ring
    have h3 : (|r| * ε) ^ 2 ≤ ν := by
      have h4 := pow_le_pow_left₀ (mul_nonneg (abs_nonneg r) hε.le) h1.le 2
      rwa [Real.sq_sqrt hν.le] at h4
    have hne : ε * r ≠ 0 := mul_ne_zero hε.ne' h0
    have hpos : 0 < (ε * r) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))
    unfold chiYr
    rw [if_neg h0]
    apply hχ.zero
    rw [le_div_iff₀ hpos, one_mul, h2]
    exact h3

/-- The stream cut vanishes at receivers with `cylR y < √ν/ε`, for every field. -/
theorem mYF_streamCut_zero_of_lt (ν ε : ℝ) (χy : ℝ → ℝ) (hχ : IsStreamCutoff χy) (hν : 0 < ν)
    (hε : 0 < ε) (Z : Vec3 → Vec3) {y : Vec3} (hy : cylR y < Real.sqrt ν / ε) :
    streamCut ν ε χy Z y = 0 := by
  have ha : 0 < Real.sqrt ν / ε := div_pos (Real.sqrt_pos.2 hν) hε
  have hnn : 0 ≤ cylR y := by unfold cylR; positivity
  have hmem : Ioo (-(Real.sqrt ν / ε)) (Real.sqrt ν / ε) ∈ 𝓝 (cylR y) :=
    Ioo_mem_nhds (by linarith) hy
  have hev : chiYr ν ε χy =ᶠ[𝓝 (cylR y)] fun _ => (0 : ℝ) :=
    Filter.eventually_of_mem hmem (fun s hs => mYF_chiYr_zero ν ε χy hχ hν hε (abs_lt.2 hs))
  have hd : deriv (chiYr ν ε χy) (cylR y) = 0 := by
    rw [hev.deriv_eq]
    simp
  have hz : chiYr ν ε χy (cylR y) = 0 :=
    mYF_chiYr_zero ν ε χy hχ hν hε (abs_lt.2 ⟨by linarith, hy⟩)
  unfold streamCut
  rw [hd, hz]
  simp

/-- The stream cut vanishes on a neighbourhood of `y` when `cylR y < √ν/ε`. -/
theorem mYF_streamCut_eventually (ν ε : ℝ) (χy : ℝ → ℝ) (hχ : IsStreamCutoff χy) (hν : 0 < ν)
    (hε : 0 < ε) (Z : Vec3 → Vec3) {y : Vec3} (hy : cylR y < Real.sqrt ν / ε) :
    streamCut ν ε χy Z =ᶠ[𝓝 y] fun _ => (0 : Vec3) := by
  have hopen : IsOpen {x : Vec3 | cylR x < Real.sqrt ν / ε} :=
    isOpen_lt (by unfold cylR; fun_prop) continuous_const
  filter_upwards [hopen.mem_nhds hy] with x hx
  exact mYF_streamCut_zero_of_lt ν ε χy hχ hν hε Z hx

/-- `dmuFree` vanishes at `y` for a field that vanishes near `y`. -/
theorem mYF_dmuFree_zero (ν μ' : ℝ) {F : Vec3 → Vec3} {y : Vec3}
    (h : F =ᶠ[𝓝 y] fun _ => (0 : Vec3)) : dmuFree ν μ' F y = 0 := by
  have hF : F y = 0 := h.eq_of_nhds
  have hD : fderiv ℝ F y = 0 := by
    rw [h.fderiv_eq]
    simp
  have hfd : fderiv ℝ F =ᶠ[𝓝 y] fderiv ℝ (fun _ => (0 : Vec3)) := h.fderiv (𝕜 := ℝ)
  have hL : vecLap F y = 0 := by
    unfold vecLap
    refine Finset.sum_eq_zero (fun j _ => ?_)
    have h2 : (fun y' : Vec3 => fderiv ℝ F y' (Pi.single j 1 : Vec3)) =ᶠ[𝓝 y] fun _ => (0 : Vec3) := by
      filter_upwards [hfd] with y' hy'
      rw [hy']
      simp
    rw [h2.fderiv_eq]
    simp
  simp [dmuFree, hF, hD, hL]

/-- The exact formula for `Y^mt` at a vector receiver, for all receivers (source 5380-5387,
5427-5432): the young case is `meanYFormula_of_shift`, the old case is zero on both sides. -/
theorem meanYFormulaVec_of (hS : MeanShiftIdentity) {c ν ε μ : ℝ} {χo χy : ℝ → ℝ}
    (hL : LHyp c ν ε μ χo χy) {M : Chart → Mat3} (hM : OldThinFinite c ν M) (y : Vec3) :
    MeanYFormula c ν ε μ χo χy M y := by
  by_cases hy : Real.sqrt ν / ε ≤ cylR y
  · exact meanYFormula_of_shift hS hL hM hy
  · have hlt : cylR y < Real.sqrt ν / ε := lt_of_not_ge hy
    have hν := hL.nu_pos
    have hε := hL.eps_pos
    have hχ := hL.chiY
    have hX : Xmt c ν ε μ χo χy M =ᶠ[𝓝 y] fun _ => (0 : Vec3) :=
      mYF_streamCut_eventually ν ε χy hχ hν hε _ hlt
    have h1 := mYF_streamCut_zero_of_lt ν ε χy hχ hν hε (youngW c ν ε μ χo M) hlt
    have h2 := mYF_dmuFree_zero ν (μ + 1)
      (mYF_streamCut_eventually ν ε χy hχ hν hε (youngW c ν ε μ χo M - youngW c ν ε (μ + 1) χo M) hlt)
    have h3 := mYF_streamCut_zero_of_lt ν ε χy hχ hν hε
      (dmuFree ν (μ + 1) (youngW c ν ε μ χo M - youngW c ν ε (μ + 1) χo M)) hlt
    unfold MeanYFormula
    rw [YmtFun_eq_dmuFree, mYF_dmuFree_zero ν (μ + 1) hX, h1, h2, h3]
    simp

/-- The exact formula `Y^mt = 𝒞_{χ_y}W_μ + [D_{μ+1},𝒞_{χ_y}](W_μ - W_{μ+1})` at every receiver,
for the standing hypotheses `LHyp` and a thin tensor with finite `N₀` (`MeanYFormulaAt`). -/
theorem meanYFormulaAt_of (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (hS : MeanShiftIdentity) (hmZ : 3 / 2 < K.mZ) (hγ : 0 < gRate Pl) :
    MeanYFormulaAt Pl K L μ := by
  intro hL T τ y _hy
  obtain ⟨C, k, hC⟩ := sourceLN0 K.mZ (gRate Pl) hmZ hγ
  have hfin : OldThinFinite (cOf L.ν) L.ν (thinRep T) :=
    (hC (cOf L.ν) L.ν (L.ρb Pl K) hL.c_pos hL.nu_pos hL.nu_le T).1
  unfold mnY mnYA mnYB Ymean mtField
  rw [← WithLp.toLp_add]
  congr 1
  exact meanYFormulaVec_of hS hL hfin (WithLp.ofLp y)

/-- **`PartIII-b:C/rep/8/1/1/2/2`**: the exact formula for `Y^mt` along the levels (source
5380-5387, 5427-5432), from `meanShiftIdentity` (task `/2a`) and `meanYFormulaAt_of`. -/
theorem meanYFormulaSeq (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.MeanYFormula := by
  unfold SeqData.MeanYFormula
  exact Filter.Eventually.of_forall (fun n z _ =>
    meanYFormulaAt_of D.Pl D.K (D.level n) (D.mu n z) meanShiftIdentity hst.mZ_gt hst.gamma_pos)

end UnforcedLeray.Short.PartIIIb.Concrete
