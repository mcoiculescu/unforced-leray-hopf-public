import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_7
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_7.Decay

/-!
# `BgVL4` from the `L⁴` bounds of the raw and inlet parts (task `PartIII-b:C/ward/13/7/1`)

Source of record: `the November 2 reference manuscript` (73 pages).
The ball split is `V = p.raw + Σᵢ p.coord z i • p.inlet i` (`IsBallSplit`, 2664-2672).
The analytic input is the decay of the raw part and of the inlet columns (2563-2601, 2607-2608),
which is not in Lean; it is isolated as the Prop `RawInletL4` below.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (Params)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- A family `F(τ)` of spatial fields that is differentiable with `F(τ)`, `DF(τ)` bounded in
`L⁴(ℝ³)` uniformly in the phase `τ`. -/
def L4Family (F : ℝ → UnforcedLeray.SpatialField) : Prop :=
  ∃ C : ℝ, ∀ τ : ℝ, Differentiable ℝ (F τ) ∧
    eLpNorm (F τ) 4 volume ≤ ENNReal.ofReal C ∧
      eLpNorm (fun y => fderiv ℝ (F τ) y) 4 volume ≤ ENNReal.ofReal C

/-- **Inverse-distance decay of a family of spatial fields** (source 2563-2601, `|D^jF| ≲ |y|^{-1-j}`
at large `|y|`, combined with boundedness on bounded `|y|`; stated as `(1+|y|)^{-1-j}` bounds):
`F(τ)` is differentiable and `‖F(τ,y)‖`, `‖DF(τ,y)‖ ≤ C (1+|y|)⁻¹` uniformly in `τ`. -/
def InvDecay (F : ℝ → UnforcedLeray.SpatialField) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, Differentiable ℝ (F τ) ∧
    ∀ y, ‖F τ y‖ ≤ C * (1 + ‖y‖)⁻¹ ∧ ‖fderiv ℝ (F τ) y‖ ≤ C * (1 + ‖y‖)⁻¹

/-- **Decay of the raw part at the levels of the contraction ball** (source 2563-2601, 2607-2608). -/
def RawDecayAtLevels : Prop :=
  AtBallLevels fun p _ _ _ => InvDecay p.raw

/-- **Decay of the inlet columns at the levels of the contraction ball** (source 2563-2601,
2607-2608; the columns `E_i` of the frozen inlet). -/
def InletDecayAtLevels : Prop :=
  AtBallLevels fun p _ _ _ => ∀ i : Fin 2, InvDecay (p.inlet i)

theorem InvDecay.l4 {F : ℝ → UnforcedLeray.SpatialField} (h : InvDecay F) : L4Family F := by
  obtain ⟨C, hC, hF⟩ := h
  refine ⟨C * decayK, fun τ => ⟨(hF τ).1, eLpNorm_le_of_decay _ hC (fun y => ((hF τ).2 y).1),
    eLpNorm_le_of_decay _ hC (fun y => ((hF τ).2 y).2)⟩⟩

theorem L4Family.add {F G : ℝ → UnforcedLeray.SpatialField} (hF : L4Family F)
    (hG : L4Family G) : L4Family (fun τ y => F τ y + G τ y) := by
  obtain ⟨CF, hCF⟩ := hF
  obtain ⟨CG, hCG⟩ := hG
  refine ⟨|CF| + |CG|, fun τ => ?_⟩
  obtain ⟨hFd, hF0, hF1⟩ := hCF τ
  obtain ⟨hGd, hG0, hG1⟩ := hCG τ
  have hsum : ENNReal.ofReal (|CF| + |CG|) = ENNReal.ofReal |CF| + ENNReal.ofReal |CG| :=
    ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
  have hle1 : ENNReal.ofReal CF ≤ ENNReal.ofReal |CF| := ENNReal.ofReal_le_ofReal (le_abs_self _)
  have hle2 : ENNReal.ofReal CG ≤ ENNReal.ofReal |CG| := ENNReal.ofReal_le_ofReal (le_abs_self _)
  have hd : Differentiable ℝ (fun y => F τ y + G τ y) := hFd.add hGd
  refine ⟨hd, ?_, ?_⟩
  · calc eLpNorm (fun y => F τ y + G τ y) 4 volume
        ≤ eLpNorm (F τ) 4 volume + eLpNorm (G τ) 4 volume :=
          eLpNorm_add_le hFd.continuous.aestronglyMeasurable hGd.continuous.aestronglyMeasurable
            (by norm_num)
      _ ≤ _ := by rw [hsum]; exact add_le_add (hF0.trans hle1) (hG0.trans hle2)
  · have hfd : (fun y => fderiv ℝ (fun y' => F τ y' + G τ y') y) =
        fun y => fderiv ℝ (F τ) y + fderiv ℝ (G τ) y := by
      funext y; exact fderiv_add (hFd y) (hGd y)
    rw [hfd]
    have m1 : AEStronglyMeasurable (fun y => fderiv ℝ (F τ) y) volume :=
      (measurable_fderiv ℝ (F τ)).aestronglyMeasurable
    have m2 : AEStronglyMeasurable (fun y => fderiv ℝ (G τ) y) volume :=
      (measurable_fderiv ℝ (G τ)).aestronglyMeasurable
    refine (eLpNorm_add_le (p := (4 : ℝ≥0∞)) m1 m2 (by norm_num)).trans ?_
    rw [hsum]
    exact add_le_add (hF1.trans hle1) (hG1.trans hle2)

theorem L4Family.smul {F : ℝ → UnforcedLeray.SpatialField} (c : ℝ) (hF : L4Family F) :
    L4Family (fun τ y => c • F τ y) := by
  obtain ⟨CF, hCF⟩ := hF
  refine ⟨|c| * |CF|, fun τ => ?_⟩
  obtain ⟨hFd, hF0, hF1⟩ := hCF τ
  have hc : ‖c‖ₑ = ENNReal.ofReal |c| := Real.enorm_eq_ofReal_abs c
  have hmul : ENNReal.ofReal (|c| * |CF|) = ENNReal.ofReal |c| * ENNReal.ofReal |CF| :=
    ENNReal.ofReal_mul (abs_nonneg _)
  have hle : ENNReal.ofReal CF ≤ ENNReal.ofReal |CF| := ENNReal.ofReal_le_ofReal (le_abs_self _)
  refine ⟨hFd.const_smul c, ?_, ?_⟩
  · have h := eLpNorm_const_smul (μ := volume) c (F τ) 4
    change eLpNorm (c • F τ) 4 volume ≤ _
    rw [h, hc, hmul]
    exact mul_le_mul' le_rfl (hF0.trans hle)
  · have hfd : (fun y => fderiv ℝ (fun y' => c • F τ y') y) =
        fun y => c • fderiv ℝ (F τ) y := by
      funext y; exact fderiv_const_smul (hFd y) c
    rw [hfd]
    have h := eLpNorm_const_smul (μ := volume) c (fun y => fderiv ℝ (F τ) y) 4
    change eLpNorm (c • fun y => fderiv ℝ (F τ) y) 4 volume ≤ _
    rw [h, hc, hmul]
    exact mul_le_mul' le_rfl (hF1.trans hle)

/-- **`BgVL4` from the decay of the raw and inlet parts.** The ball split
`V = raw + Σᵢ coordᵢ • inletᵢ` (`IsBallSplit`) with fixed coefficients `coord z i` gives `V(τ)`,
`DV(τ)` bounded in `L⁴`. -/
theorem bgVL4_of (hRaw : RawDecayAtLevels) (hInl : InletDecayAtLevels) : BgVL4 := by
  intro Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₁, hν₁, H1⟩ := hRaw Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₂, hν₂, H2⟩ := hInl Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  refine ⟨min ν₁ ν₂, lt_min hν₁ hν₂, fun p d hreg hν hS hq' V rb pres hb hU => ?_⟩
  have hR := H1 p d hreg (hν.trans (min_le_left _ _)) hS hq' V rb pres hb hU
  have hI := H2 p d hreg (hν.trans (min_le_right _ _)) hS hq' V rb pres hb hU
  obtain ⟨z, _, hVz, _, _⟩ := hb
  have hfun : V = fun τ y => p.raw τ y +
      (p.coord z 0 • p.inlet 0 τ y + p.coord z 1 • p.inlet 1 τ y) := by
    funext τ y
    rw [hVz τ y, Fin.sum_univ_two]
  rw [hfun]
  exact hR.l4.add (((hI 0).l4.smul (p.coord z 0)).add ((hI 1).l4.smul (p.coord z 1)))

end UnforcedLeray.Short.PartIIIb.Concrete
