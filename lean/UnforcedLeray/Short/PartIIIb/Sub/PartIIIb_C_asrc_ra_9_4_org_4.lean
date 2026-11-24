import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_4.Defs

/-!
# `PartIII-b:C/asrc/ra/9/4/org/4` : decomposition of `PsiKCellL2`

Source `the November 2 reference manuscript`
lines 5063-5079, 4978, 5024.  `(𝒦+2)Ψ_A = η∂_ηΨ_A + 2s∂_sΨ_A + 2Ψ_A`, so the cell `L²` norm is
controlled by the three pieces `|η||∂_ηΨ_A|`, `2s|∂_sΨ_A|`, `|Ψ_A|` (`PsiADerivCell`, the
Gaussian lattice-sum core with termwise differentiation); the rest is `psiKCellL2_of`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- **Gaussian lattice-sum cell bounds for the three pieces of `(𝒦+2)Ψ_A`** (source 5063-5079):
the cell `L²` norms of `|η|·|∂_ηΨ_A|`, `2s|∂_sΨ_A|` and `|Ψ_A|` are each
`≤ P_ν M(A)(s^{3/2}+s^{5/2})`, with the three functions a.e. measurable.  Needs termwise
differentiation of `Ψ_A = Σ_j (A^y_mer x_j)·∇p_j` with the Gaussian envelope (4978). -/
def PsiADerivCell (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
    ∀ (ν : ℝ), 0 < ν → ν ≤ ν₀ → ∀ A : ℝ → Mat3, IsAffElem as A →
      ∀ s : ℝ, 0 < s → s ≤ (11 / 10) / ν →
        let B := C * ν⁻¹ ^ k * affM ν χf A * (s ^ (3 / 2 : ℝ) + s ^ (5 / 2 : ℝ))
        let a : ℝ × ℝ → ℝ := fun x => |x.2| * |fderiv ℝ (PsiA ν χf A s) x (ei 1)|
        let b : ℝ × ℝ → ℝ := fun x => 2 * s * |deriv (fun s' => PsiA ν χf A s' x) s|
        let c : ℝ × ℝ → ℝ := fun x => |PsiA ν χf A s x|
        AEMeasurable a (UnforcedLeray.Cyl.avgμ (cOf ν)) ∧
        AEMeasurable b (UnforcedLeray.Cyl.avgμ (cOf ν)) ∧
        AEMeasurable c (UnforcedLeray.Cyl.avgμ (cOf ν)) ∧
        (∫⁻ x, ENNReal.ofReal (a x ^ 2) ∂(UnforcedLeray.Cyl.avgμ (cOf ν)) ≤ ENNReal.ofReal (B ^ 2)) ∧
        (∫⁻ x, ENNReal.ofReal (b x ^ 2) ∂(UnforcedLeray.Cyl.avgμ (cOf ν)) ≤ ENNReal.ofReal (B ^ 2)) ∧
        (∫⁻ x, ENNReal.ofReal (c x ^ 2) ∂(UnforcedLeray.Cyl.avgμ (cOf ν)) ≤ ENNReal.ofReal (B ^ 2))

theorem psiKCellL2_of (as : ℝ) (χf : ℝ → ℝ) (h : PsiADerivCell as χf) : PsiKCellL2 as χf := by
  intro hχ
  obtain ⟨C, k, ν₀, hν₀, H⟩ := h hχ
  refine ⟨6 * C, k, ν₀, hν₀, fun ν hν hνν A hA s hs hs1 => ?_⟩
  obtain ⟨ha, hb, hc, ia, ib, ic⟩ := H ν hν hνν A hA s hs hs1
  set μ := UnforcedLeray.Cyl.avgμ (cOf ν)
  set B := C * ν⁻¹ ^ k * affM ν χf A * (s ^ (3 / 2 : ℝ) + s ^ (5 / 2 : ℝ)) with hB
  set a : ℝ × ℝ → ℝ := fun x => |x.2| * |fderiv ℝ (PsiA ν χf A s) x (ei 1)| with hadef
  set b : ℝ × ℝ → ℝ := fun x => 2 * s * |deriv (fun s' => PsiA ν χf A s' x) s| with hbdef
  set c : ℝ × ℝ → ℝ := fun x => |PsiA ν χf A s x| with hcdef
  have hpt : ∀ x, ENNReal.ofReal (|Kop (fun s' y => PsiA ν χf A s' y) s x + 2 * PsiA ν χf A s x| ^ 2)
      ≤ 12 * (ENNReal.ofReal (a x ^ 2) + ENNReal.ofReal (b x ^ 2) + ENNReal.ofReal (c x ^ 2)) := by
    intro x
    have h1 : |Kop (fun s' y => PsiA ν χf A s' y) s x + 2 * PsiA ν χf A s x| ≤ a x + b x + 2 * c x := by
      unfold Kop
      have e : (x.2 * fderiv ℝ (PsiA ν χf A s) x (ei 1) + 2 * s * deriv (fun s' => PsiA ν χf A s' x) s
          + 2 * PsiA ν χf A s x) = x.2 * fderiv ℝ (PsiA ν χf A s) x (ei 1)
          + 2 * s * deriv (fun s' => PsiA ν χf A s' x) s + 2 * PsiA ν χf A s x := rfl
      calc _ ≤ |x.2 * fderiv ℝ (PsiA ν χf A s) x (ei 1)| + |2 * s * deriv (fun s' => PsiA ν χf A s' x) s|
              + |2 * PsiA ν χf A s x| := abs_add_three _ _ _
        _ = a x + b x + 2 * c x := by
            simp only [hadef, hbdef, hcdef, abs_mul, abs_two, abs_of_pos hs]
    have ha0 : 0 ≤ a x := by simp only [hadef]; positivity
    have hb0 : 0 ≤ b x := by simp only [hbdef]; positivity
    have hc0 : 0 ≤ c x := by simp only [hcdef]; positivity
    have h2 : |Kop (fun s' y => PsiA ν χf A s' y) s x + 2 * PsiA ν χf A s x| ^ 2
        ≤ 12 * (a x ^ 2 + b x ^ 2 + c x ^ 2) := by
      have := pow_le_pow_left₀ (abs_nonneg _) h1 2
      nlinarith [sq_nonneg (a x - b x), sq_nonneg (a x - 2 * c x), sq_nonneg (b x - 2 * c x)]
    calc _ ≤ ENNReal.ofReal (12 * (a x ^ 2 + b x ^ 2 + c x ^ 2)) := ENNReal.ofReal_le_ofReal h2
      _ = 12 * (ENNReal.ofReal (a x ^ 2) + ENNReal.ofReal (b x ^ 2) + ENNReal.ofReal (c x ^ 2)) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_add (by positivity) (by positivity)]
          simp
  have hma : AEMeasurable (fun x => ENNReal.ofReal (a x ^ 2)) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable (ha.pow_const 2)
  have hmb : AEMeasurable (fun x => ENNReal.ofReal (b x ^ 2)) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hb.pow_const 2)
  calc _ ≤ ∫⁻ x, 12 * (ENNReal.ofReal (a x ^ 2) + ENNReal.ofReal (b x ^ 2) + ENNReal.ofReal (c x ^ 2)) ∂μ :=
        lintegral_mono hpt
    _ = 12 * (∫⁻ x, ENNReal.ofReal (a x ^ 2) ∂μ + ∫⁻ x, ENNReal.ofReal (b x ^ 2) ∂μ
          + ∫⁻ x, ENNReal.ofReal (c x ^ 2) ∂μ) := by
        have e2 : ∫⁻ x, (ENNReal.ofReal (a x ^ 2) + ENNReal.ofReal (b x ^ 2)) ∂μ
            = ∫⁻ x, ENNReal.ofReal (a x ^ 2) ∂μ + ∫⁻ x, ENNReal.ofReal (b x ^ 2) ∂μ :=
          lintegral_add_left' hma _
        have e1 : ∫⁻ x, (ENNReal.ofReal (a x ^ 2) + ENNReal.ofReal (b x ^ 2)
              + ENNReal.ofReal (c x ^ 2)) ∂μ
            = ∫⁻ x, (ENNReal.ofReal (a x ^ 2) + ENNReal.ofReal (b x ^ 2)) ∂μ
              + ∫⁻ x, ENNReal.ofReal (c x ^ 2) ∂μ :=
          lintegral_add_left' (hma.add hmb) _
        rw [lintegral_const_mul' _ _ (by simp), e1, e2]
    _ ≤ 12 * (ENNReal.ofReal (B ^ 2) + ENNReal.ofReal (B ^ 2) + ENNReal.ofReal (B ^ 2)) := by
        gcongr
    _ = ENNReal.ofReal (36 * B ^ 2) := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        have h36 : ENNReal.ofReal 36 = 36 := by simpa using ENNReal.ofReal_natCast 36
        rw [h36]; ring
    _ = ENNReal.ofReal (((6 * C) * ν⁻¹ ^ k * affM ν χf A * (s ^ (3 / 2 : ℝ) + s ^ (5 / 2 : ℝ))) ^ 2) := by
        congr 1; rw [hB]; ring

end UnforcedLeray.Short.PartIIIb.Concrete
