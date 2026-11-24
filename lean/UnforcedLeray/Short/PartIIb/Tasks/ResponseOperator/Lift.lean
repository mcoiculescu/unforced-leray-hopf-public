import UnforcedLeray.Short.PartIIb.Tasks.BodyLift.Norm
import UnforcedLeray.Short.PartIIb.Tasks.BodyLift.Linear_3
import UnforcedLeray.Short.PartIIb.Tasks.BodyLift.Linear_4
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.NvCInYr
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.DriftNoSwirl.Leaf7
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.YqOfFields
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.YqRealSymm
import UnforcedLeray.Short.PartIIb.Bridge.Dict

/-!
# Helper `ResponseOperator/Lift`: lifting `HpR p.c` into `Yq p.period q0E`

For `f : HpR p.c`, `NvC p.R (toProf p.c f)` lies in `IsInYr p.period bgp` (`nvCInYr_proof`), so it
has a unique representative `liftY p f : Yq p.period q0E` (`yqOfFields`), which is `ℝ`-linear in `f`
(`blNvLin_proof`, `BLRepLinAux`), lies in `realSub p.period q0E` (`yqRealSymm`), and has norm
`‖liftY p f‖ = (π R²)^{1/p} ‖f‖` (`phaseLpNorm_NvC`, `hNorm_toProf`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.RespOp

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412 UnforcedLeray.Short.IIb

theorem hasRepY_iff_hasRep {P : ℝ} [Fact (0 < P)] {F : Yq P q0E} {W : ℝ × Space → CVec3} :
    HasRepY F W ↔ HasRep F W :=
  ⟨fun h => ⟨h.meas, h.slice⟩, fun h => ⟨h.meas, h.slice⟩⟩

theorem hasRepY_rep {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)] (u : Yq P q) :
    HasRepY u (fun x : ℝ × Space => rep u x.1 x.2) :=
  ⟨(stronglyMeasurable_rep u).aestronglyMeasurable,
    Filter.Eventually.of_forall fun τ => rep_slice u τ⟩

theorem rep_ae_eq_of_hasRepY {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)] {u : Yq P q}
    {W : ℝ × Space → CVec3} (hW : HasRepY u W) :
    ∀ᵐ x : ℝ × Space, rep u x.1 x.2 = W x :=
  PhaseFundHelp.hasRepY_ae_eq (hasRepY_rep u) hW

theorem hasRepY_congr_ae {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)] {u : Yq P q}
    {W W' : ℝ × Space → CVec3} (hW : HasRepY u W) (heq : ∀ᵐ x : ℝ × Space, W' x = W x) :
    HasRepY u W' := by
  have hmeas : AEStronglyMeasurable W' volume := hW.meas.congr (Filter.EventuallyEq.symm heq)
  have hprod : ∀ᵐ x ∂((volume : Measure ℝ).prod (volume : Measure Space)), W' x = W x := by
    rw [← Measure.volume_eq_prod]
    exact heq
  have hsl := Measure.ae_ae_of_ae_prod (p := fun z : ℝ × Space => W' z = W z) hprod
  refine ⟨hmeas, ?_⟩
  filter_upwards [hsl, hW.slice] with τ h1 h2
  exact Filter.EventuallyEq.trans h1 h2

theorem inHr_toProf {c : ℝ} (hc : 0 < c) (f : HpR c) : InHr c bgp (toProf c f) :=
  ⟨toProf_periodic hc f, toProf_aestronglyMeasurable hc f, by
    rw [hNorm_toProf hc f]
    exact enorm_lt_top⟩

theorem isInYr_nvC_toProf (p : Params) (f : HpR p.c) :
    IsInYr p.period bgp (NvC p.R (toProf p.c f)) := by
  have hper : p.period = 2 * p.ε * p.c := rfl
  have hR : p.R = p.ε⁻¹ := rfl
  rw [hper, hR]
  exact nvCInYr_proof p.c p.ε bgp (toProf p.c f) p.c_pos p.ε_pos (by norm_num [bgp])
    (inHr_toProf p.c_pos f)

/-- The `Yq p.period q0E` representative of `NvC p.R (toProf p.c f)`. -/
def liftY (p : Params) (f : HpR p.c) : Yq p.period q0E :=
  (yqOfFields p.period (NvC p.R (toProf p.c f)) (isInYr_nvC_toProf p f)).choose

theorem hasRep_liftY (p : Params) (f : HpR p.c) :
    HasRep (liftY p f) (NvC p.R (toProf p.c f)) :=
  (yqOfFields p.period (NvC p.R (toProf p.c f)) (isInYr_nvC_toProf p f)).choose_spec.1

theorem hasRepY_liftY (p : Params) (f : HpR p.c) :
    HasRepY (liftY p f) (NvC p.R (toProf p.c f)) :=
  hasRepY_iff_hasRep.2 (hasRep_liftY p f)

theorem norm_liftY (p : Params) (f : HpR p.c) :
    ‖liftY p f‖ = (Real.pi * p.R ^ 2) ^ (1 / bgp) * ‖f‖ := by
  have hn : ‖liftY p f‖ = (phaseLpNorm p.period bgp (NvC p.R (toProf p.c f))).toReal :=
    (yqOfFields p.period (NvC p.R (toProf p.c f)) (isInYr_nvC_toProf p f)).choose_spec.2
  have hc : 0 < p.c := p.c_pos
  have hε : 0 < p.ε := p.ε_pos
  have hr : 0 < bgp := by norm_num [bgp]
  have h3 : phaseLpNorm p.period bgp (NvC p.R (toProf p.c f)) =
      ENNReal.ofReal ((Real.pi * p.R ^ 2) ^ (1 / bgp)) * hNorm p.c bgp (toProf p.c f) :=
    phaseLpNorm_NvC hc hr hε (toProf p.c f) (toProf_periodic hc f)
      (toProf_aestronglyMeasurable hc f)
  have h1 : phaseLpNorm p.period bgp (NvC p.R (toProf p.c f)) =
      ENNReal.ofReal ((Real.pi * p.R ^ 2) ^ (1 / bgp)) * ‖f‖ₑ := by
    rw [h3, hNorm_toProf hc f]
  have hK : 0 ≤ (Real.pi * p.R ^ 2) ^ (1 / bgp) := by
    have : 0 < p.R := p.R_pos
    positivity
  rw [hn, h1, ENNReal.toReal_mul, ENNReal.toReal_ofReal hK, toReal_enorm]

theorem imM_toProf_eq_zero {c : ℝ} (f : HpR c) (z : Coord) : imM (toProf c f z) = 0 := by
  ext i
  simp [imM, toProf]

theorem nvC_toProf_eq_realC {R c : ℝ} (f : HpR c) (x : ℝ × Space) :
    NvC R (toProf c f) x = realC (Axi.Nv R (fun z => reM (toProf c f z)) x.1 x.2) := by
  have him : (fun z => imM (toProf c f z)) = 0 := funext (imM_toProf_eq_zero f)
  unfold NvC
  rw [him]
  have h0 : Axi.Nv R 0 x.1 x.2 = 0 := by simp [Axi.Nv, Axi.frameL_apply]
  rw [h0, linear3_realC_zero, smul_zero, add_zero]

theorem liftY_mem_realSub (p : Params) (f : HpR p.c) : liftY p f ∈ realSub p.period q0E :=
  yqRealSymm p.period (liftY p f) (NvC p.R (toProf p.c f)) (hasRep_liftY p f)
    (fun x => ⟨_, nvC_toProf_eq_realC f x⟩)

theorem liftY_add (p : Params) (f₁ f₂ : HpR p.c) :
    liftY p (f₁ + f₂) = liftY p f₁ + liftY p f₂ := by
  have h1 := rep_ae_eq_of_hasRepY (hasRepY_liftY p f₁)
  have h2 := rep_ae_eq_of_hasRepY (hasRepY_liftY p f₂)
  have hrep := BLRepLinAux.rep_add_ae (liftY p f₁) (liftY p f₂)
  have hlin := (blNvLin_proof p.R p.c p.c_pos f₁ f₂).1
  have heq : ∀ᵐ x : ℝ × Space,
      NvC p.R (toProf p.c (f₁ + f₂)) x = rep (liftY p f₁ + liftY p f₂) x.1 x.2 := by
    filter_upwards [hlin, hrep, h1, h2] with x e1 e2 e3 e4
    rw [e1, e2, e3, e4]
  exact hasRepY_unique (hasRepY_liftY p (f₁ + f₂))
    (hasRepY_congr_ae (hasRepY_rep (liftY p f₁ + liftY p f₂)) heq)

theorem liftY_smul (p : Params) (a : ℝ) (f : HpR p.c) :
    liftY p (a • f) = a • liftY p f := by
  have h1 := rep_ae_eq_of_hasRepY (hasRepY_liftY p f)
  have hrep := BLRepLinAux.rep_smul_ae a (liftY p f)
  have hlin := (blNvLin_proof p.R p.c p.c_pos f f).2 a
  have heq : ∀ᵐ x : ℝ × Space,
      NvC p.R (toProf p.c (a • f)) x = rep (a • liftY p f) x.1 x.2 := by
    filter_upwards [hlin, hrep, h1] with x e1 e2 e3
    rw [e1, e2, e3]
  exact hasRepY_unique (hasRepY_liftY p (a • f))
    (hasRepY_congr_ae (hasRepY_rep (a • liftY p f)) heq)

end UnforcedLeray.Short.IIb.RespOp

end
