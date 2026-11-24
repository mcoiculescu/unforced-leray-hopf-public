import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4.Assembly
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_1Org
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4.WardGainMarginFalse

/-!
# Bridge lemmas for the sum `S_far T + Y[T]` on thin sources

Source `the November 2 reference manuscript` 5303-5316, 5569-5605, 5688-5689,
4161-4199.  The source never bounds `S_far` or `Y` alone in the gain norms; the margins
`γ/18` (late output) and `γ/10` (early source) of 5594-5599 are for the pieces of the sum.  This
file holds the generic bin lemmas (triangle inequality for `binNorm`, ungained velocity bin to
gained bin norm) and the Props that are new in the plateau analysis.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. Generic bin lemmas -/

theorem binUpper_succ (S h : ℝ) (j : ℕ) :
    binUpper S h (j + 1) = binUpper S h j * Real.exp (-h) := by
  unfold binUpper
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  push_cast
  ring

theorem binUpper_le {S h : ℝ} (hS : 0 ≤ S) (hh : 0 ≤ h) (j : ℕ) : binUpper S h j ≤ S := by
  unfold binUpper
  have : Real.exp (-(h * j)) ≤ 1 := Real.exp_le_one_iff.2 (by
    have : 0 ≤ h * (j : ℝ) := by positivity
    linarith)
  nlinarith

theorem binUpper_pos {S h : ℝ} (hS : 0 < S) (j : ℕ) : 0 < binUpper S h j := by
  unfold binUpper; positivity

theorem binNorm_add_le (c γ ν S h : ℝ) (j : ℕ) (φ ψ : VelG c γ ν) :
    binNorm c γ ν S h j (φ + ψ) ≤ binNorm c γ ν S h j φ + binNorm c γ ν S h j ψ := by
  unfold binNorm
  set μ := (bodyMeasure c γ ν).restrict (binSet S h j) with hμ
  have hle : μ ≤ bodyMeasure c γ ν := Measure.restrict_le_self
  have hfin : ∀ χ : VelG c γ ν, eLpNorm (χ : Chart → Merid) 2 μ ≠ ⊤ := fun χ =>
    ((eLpNorm_mono_measure _ hle).trans_lt (Lp.eLpNorm_lt_top χ)).ne
  have hms : ∀ χ : VelG c γ ν, AEStronglyMeasurable (χ : Chart → Merid) μ := fun χ =>
    (Lp.aestronglyMeasurable χ).mono_measure hle
  have hae : ⇑(φ + ψ) =ᵐ[μ] ⇑φ + ⇑ψ := ae_restrict_of_ae (Lp.coeFn_add φ ψ)
  rw [eLpNorm_congr_ae hae]
  have h1 := eLpNorm_add_le (hms φ) (hms ψ) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h2 : eLpNorm (⇑φ + ⇑ψ) 2 μ ≠ ⊤ :=
    (h1.trans_lt (ENNReal.add_lt_top.2 ⟨(hfin φ).lt_top, (hfin ψ).lt_top⟩)).ne
  rw [← ENNReal.toReal_add (hfin φ) (hfin ψ)]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin φ, hfin ψ⟩) h1

/-- The normalized ungained velocity norm on the bin is `√π` times the `ageμ` bin norm. -/
theorem velBin_eq (c S h : ℝ) (j : ℕ) (F : Chart → Merid) :
    velBin c (binUpper S h (j + 1)) (binUpper S h j) F =
      ENNReal.ofReal (Real.sqrt Real.pi) * ageNormBin c S h j F := by
  unfold velBin ageNormBin
  have hset : {p : Chart | binUpper S h (j + 1) < p.1 ∧ p.1 ≤ binUpper S h j} = binSet S h j := rfl
  rw [hset]
  unfold srcMeasure
  rw [Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ENNReal.ofReal_rpow_of_nonneg Real.pi_pos.le (by norm_num), ← Real.sqrt_eq_rpow]

/-- **Bin velocity to gained bin norm**: `BinNormToAge` and `velBin_eq` give
`‖φ‖_{bin j} ≤ G · velBin` when `g⁻¹ ≤ G` on the bin. -/
theorem binNorm_le_velBin (hBN : BinNormToAge) (c γ ν S h : ℝ) (j : ℕ) (φ : VelG c γ ν)
    (F : Chart → Merid) (G : ℝ) (hF : (φ : Chart → Merid) =ᵐ[bodyMeasure c γ ν] F) (hG : 0 ≤ G)
    (hginv : ∀ p ∈ binSet S h j, ginv γ ν p ≤ G) :
    ENNReal.ofReal (binNorm c γ ν S h j φ) ≤
      ENNReal.ofReal G * velBin c (binUpper S h (j + 1)) (binUpper S h j) F := by
  have h1 := hBN c γ ν S h j φ F G hF hG hginv
  rw [velBin_eq, ← mul_assoc, ← ENNReal.ofReal_mul hG]
  convert h1 using 2
  ring

/-- Real conclusion of a four-fold `ofReal` chain. -/
theorem le_of_ofReal_chain {b G A E t : ℝ} (hG : 0 ≤ G) (hA : 0 ≤ A) (hE : 0 ≤ E) (ht : 0 ≤ t)
    {vb zt : ℝ≥0∞}
    (h1 : ENNReal.ofReal b ≤ ENNReal.ofReal G * vb)
    (h2 : vb ≤ ENNReal.ofReal A * zt) (h3 : zt ≤ ENNReal.ofReal E * ENNReal.ofReal t) :
    b ≤ G * A * E * t := by
  have h4 : ENNReal.ofReal b ≤ ENNReal.ofReal G * (ENNReal.ofReal A *
      (ENNReal.ofReal E * ENNReal.ofReal t)) :=
    h1.trans (mul_le_mul' le_rfl (h2.trans (mul_le_mul' le_rfl h3)))
  have h5 : ENNReal.ofReal G * (ENNReal.ofReal A * (ENNReal.ofReal E * ENNReal.ofReal t)) =
      ENNReal.ofReal (G * A * E * t) := by
    rw [← ENNReal.ofReal_mul hE, ← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_mul hG]
    ring_nf
  rw [h5] at h4
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h4

/-- `g⁻¹ ≤ g(s_{j+1})⁻¹` on the bin `j`. -/
theorem ginv_le_on_bin {γ ν S h : ℝ} (hγ : 0 ≤ γ) (hν : 0 < ν) (hS : 0 ≤ S) (hh : 0 ≤ h)
    (j : ℕ) : ∀ p ∈ binSet S h j,
      ginv γ ν p ≤ (UnforcedLeray.Short.IIIa.gainG γ ν (binUpper S h (j + 1)))⁻¹ := by
  intro p hp
  have hup : binUpper S h (j + 1) < p.1 := hp.1
  have hu0 : 0 ≤ binUpper S h (j + 1) := by unfold binUpper; positivity
  have hgn : 0 < UnforcedLeray.Short.IIIa.gainG γ ν (binUpper S h (j + 1)) := gainG_pos' _ _ _
  unfold ginv
  refine inv_anti₀ hgn ?_
  exact gainG_mono hγ hν hu0 (le_max_of_le_left hup.le)

/-! ## 2. The early part and the Props of the plateau analysis -/

/-- The early part `(1 - χ_o)T₁` of the thin part (source 4163-4166: `χ_o` vanishes for
`ν t ≤ 6/5` and equals one for `ν t ≥ 3/2`, so this lives at ages `t ≤ 3/(2ν)`): `T_1 - χ_o T_1`. -/
def earlyPart (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (T : LStr Pl K L) :
    LStr Pl K L :=
  thinPart T - chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo (thinPart T)

/-- **Ungained `Z_1` tail norm of the thin part** (5571-5584, 5601): for `γ ≥ 0`, `ν > 0`,
`‖T₁‖_{Z_1, t ≥ a} ≤ sup_t g(t) · ‖g⁻¹T₁‖_{Z_1} ≤ e^{γ/ν}‖T‖` (`g(t) = e^{γt/(1+νt)} ≤ e^{γ/ν}`). -/
def Z1TailGained : Prop :=
  ∀ (c mZ ρb γ ν : ℝ), 0 ≤ γ → 0 < ν → ∀ (T : StrG c mZ ρb γ ν) (a : ℝ),
    z1Tail c mZ a (((thinPart T).fst : Lp Ten3 2 _) : Chart → Ten3) ≤
      ENNReal.ofReal (Real.exp (γ / ν)) * ‖T‖ₑ

/-- **Ungained `Z_1` norm of the early part** (4163-4166, 5594-5599): `(1-χ_o)T₁` vanishes for ages
`t ≥ 3/(2ν)` (`IsOutwardCutoff.one`) and `0 ≤ 1-χ_o ≤ 1`, so its ungained `Z_1` norm is at most
`g(3/(2ν))‖T‖`, where `g(3/(2ν)) = e^{3γ/(5ν)}` (early source margin `-γ/10`). -/
def EarlyZ1Gained : Prop :=
  ∀ (c mZ ρb γ ν : ℝ) {χ : ℝ → ℝ} (hχ : IsOutwardCutoff χ), 0 ≤ γ → 0 < ν →
    ∀ (T : StrG c mZ ρb γ ν) (a : ℝ),
      z1Tail c mZ a
          ((((thinPart T - chiOStr c mZ ρb γ ν hχ (thinPart T)).fst : Lp Ten3 2 _)) :
            Chart → Ten3) ≤
        ENNReal.ofReal (UnforcedLeray.Short.IIIa.gainG γ ν (3 / (2 * ν))) * ‖T‖ₑ

/-- `χ_o` acts componentwise, so the early part of a thin stress is thin. -/
def EarlyPartThin : Prop :=
  ∀ (c mZ ρb γ ν : ℝ) {χ : ℝ → ℝ} (hχ : IsOutwardCutoff χ) (T : StrG c mZ ρb γ ν),
    thinPart (thinPart T - chiOStr c mZ ρb γ ν hχ (thinPart T)) =
      thinPart T - chiOStr c mZ ρb γ ν hχ (thinPart T)

/-- **The young-old rectangle cancels** (source 4171-4199, 5303-5310, 5688-5689): on output ages
`s ≤ 4/(5ν)` (where `χ_y = 1`, `IsStreamCutoff.one`) the stream transition is
`Y = 𝒞_y W_μ + [D_{μ+1}, 𝒞_y]X_0 = W_μ = -S_μ(χ_o T)` (`ward:displacement`,
`ward:shifted-resolvent`, `ward:cutoff-source`), and every pair (output `s < 1/ν`, old source
`t ≥ 6/(5ν)`) lies in the far mask `{s < S, t > e^δ s}` (`δ < log(12/11)`, `S = ε^{-b} > 1/ν`
eventually), so `S_far(χ_o T) = S_μ(χ_o T)` there:  the coefficient of
`Y(thinPart T) + S_far(χ_o thinPart T)` vanishes a.e. on the output ages `s ≤ 4/(5ν)`. -/
def SeqData.PlateauCancel (D : SeqData) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ T : LStr D.Pl D.K (D.level n),
    ∀ᵐ p ∂(bodyMeasure (cOf (D.level n).ν) (gRate D.Pl) (D.level n).ν),
      p.1 ≤ 4 / (5 * (D.level n).ν) →
        ((wardOps D.Pl D.K (D.level n) (D.mu n z)).1 (thinPart T) : Chart → Merid) p +
          (((Sop D.Pl D.K (D.level n) (D.mu n z) - SNop D.Pl D.K (D.level n) (D.mu n z))
            (chiOStr (cOf (D.level n).ν) D.K.mZ ((D.level n).ρb D.Pl D.K) (gRate D.Pl)
              (D.level n).ν D.K.hχo (thinPart T)) : LVel D.Pl (D.level n)) : Chart → Merid) p = 0

/-! ## 3. The three gained bin Props of the sum -/

/-- **Late bins of the far mask** (5585-5605): for `ν s_{j+1} ≥ 2/3`, the gained bin norm of
`S_far(thinPart T)` is at most `C ν^{-k} e^{γ/(10ν)}(s_j^{1/2}+s_j^{3/4})‖T‖` (kernel bound with
`ε^{3/2}`, source gain `e^{γ/ν}`, output gain `g(s_{j+1}) ≥ e^{2γ/(5ν)}`; margin `-γ/18` at the
source threshold `4/5`). -/
def SeqData.FarLateBin (D : SeqData) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ∀ T : LStr D.Pl D.K (D.level n), ∀ j : ℕ,
      2 / 3 ≤ (D.level n).ν * binUpper ((D.level n).Scut D.K) D.K.hbin (j + 1) →
      binNorm (cOf (D.level n).ν) (gRate D.Pl) (D.level n).ν ((D.level n).Scut D.K)
          D.K.hbin j (sopThinFam D n z (thinPart T)) ≤
        C * (D.level n).ν⁻¹ ^ k * Real.exp ((gRate D.Pl / 10) / (D.level n).ν) *
          (binUpper ((D.level n).Scut D.K) D.K.hbin j ^ (1 / 2 : ℝ) +
            binUpper ((D.level n).Scut D.K) D.K.hbin j ^ (3 / 4 : ℝ)) * ‖T‖

/-- **Plateau bins, early source** (5303-5316, 5594-5599): for `ν s_{j+1} < 2/3`, the gained bin norm
of `S_far` of the early part `(1-χ_o)T₁` (ages `≤ 3/(2ν)`) is at most
`C ν^{-k} e^{γ/(10ν)}(s_j^{1/2}+s_j^{3/4})‖T‖` (kernel bound with `ε^{3/2}`, source gain
`≤ g(3/(2ν)) = e^{3γ/(5ν)}`, output gain `≥ 1`; margin `-γ/10`). -/
def SeqData.FarEarlyBin (D : SeqData) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ∀ T : LStr D.Pl D.K (D.level n), ∀ j : ℕ,
      (D.level n).ν * binUpper ((D.level n).Scut D.K) D.K.hbin (j + 1) < 2 / 3 →
      binNorm (cOf (D.level n).ν) (gRate D.Pl) (D.level n).ν ((D.level n).Scut D.K)
          D.K.hbin j (sopThinFam D n z (earlyPart D.Pl D.K (D.level n) T)) ≤
        C * (D.level n).ν⁻¹ ^ k * Real.exp ((gRate D.Pl / 10) / (D.level n).ν) *
          (binUpper ((D.level n).Scut D.K) D.K.hbin j ^ (1 / 2 : ℝ) +
            binUpper ((D.level n).Scut D.K) D.K.hbin j ^ (3 / 4 : ℝ)) * ‖T‖

/-- The sum `ageVel = (S_μ - S_N) + Y` as a thin-source family. -/
def ageThinFam : ThinFam := fun D n z => sopThinFam D n z + wardThinFam D n z

theorem ageThinFam_apply (D : SeqData) (n : ℕ) (z : ℝ) (x : LStr D.Pl D.K (D.level n)) :
    ageThinFam D n z x = ageVel D.Pl D.K (D.level n) (D.mu n z) x := rfl

end UnforcedLeray.Short.PartIIIb.Concrete

end
