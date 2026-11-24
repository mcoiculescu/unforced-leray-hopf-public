import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_5

/-!
# `DictVel` decomposed (task `PartIII-b:C/near/pins/3/5/1`)

Source `the November 2 reference manuscript`
lines 2666-2668 (chart of the similarity variable `y`), 2683 (`𝒩_v b = √s b`), 1640-1641,
1675-1677.  The lift `liftVec g` lives in the unit-ring variable `x = εy`; `velPhys` in `y`.
Five true leaves (dilation is quasi-measure-preserving; the profile of `g` is the chart
profile a.e.; the chart, frame and scalar identities at `x = εy`) give `DictVel` with
`κ = √(2π) ε`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC SpaceC X PSpace outerS physRes liftVec)

/-- **Leaf (dilation QMP)** (source 2666-2668): `(τ, y) ↦ (ε y, τ mod P)` is quasi-measure
preserving `ℝ × ℝ³ → PSpace P` for `ε ≠ 0` (`Measure.quasiMeasurePreserving_smul`, the covering
`ℝ → AddCircle P` is QMP, `QuasiMeasurePreserving.prodMap`, `measurePreserving_swap`). -/
def DictQmp : Prop :=
  ∀ (P ε : ℝ) [Fact (0 < P)], ε ≠ 0 →
    Measure.QuasiMeasurePreserving
      (fun x : ℝ × Space => ((ε • x.2, (x.1 : AddCircle P)) : PSpace P)) volume volume

/-- **Leaf (profile a.e.)** (source 1640-1641, 2666-2668; `ChartRep`, `B0223.map_liftDensity`):
for `g` with real chart form `f`, almost every point of `PSpace P` has
`g (cellChart ε c (toCell P z)) = merC (f (cellPt c (cellChart ε c (toCell P z))))`
(push `ChartRep` along `map_liftDensity`; the density is nonzero off `radius = 0`, a null set). -/
def DictAe : Prop :=
  ∀ (ε c P : ℝ) [Fact (0 < P)], 0 < ε → 0 < c → P = 2 * ε * c →
    ∀ (g : HSpace c MeridC) (f : Chart → Axi.Merid), ChartRep c g f →
      ∀ᵐ z ∂(volume : Measure (PSpace P)),
        (g : Profile → MeridC) (UnforcedLeray.B0220.cellChart ε c (UnforcedLeray.B0223.toCell P z)) =
          merC (f (cellPt c
            (UnforcedLeray.B0220.cellChart ε c (UnforcedLeray.B0223.toCell P z))))

/-- **Leaf (chart)** (source 2666-2668): at `x = ε y` the recentred chart point of `(ε y, τ)`
is the chart point of `y`: `perExt c f (Axi.chart ε⁻¹ τ y) = f (cellPt c (cellChart ε c (toCell P (ε y, τ))))`
(`toCell` shifts `τ` by `k P`, `cellQ` by `-k c`, `reduceIoc`, `cellRep`, `chartOf_eq_ring`). -/
def DictChart : Prop :=
  ∀ (ε c P : ℝ) [Fact (0 < P)], 0 < ε → 0 < c → P = 2 * ε * c →
    ∀ (f : Chart → Axi.Merid) (y : Space), y ∉ Axi.axis → ∀ τ : ℝ,
      Axi.perExt c f (Axi.chart ε⁻¹ τ y) =
        f (cellPt c (UnforcedLeray.B0220.cellChart ε c
          (UnforcedLeray.B0223.toCell P ((ε • y, (τ : AddCircle P)) : PSpace P))))

/-- **Leaf (frame)** (source 2683): `frameC (ε y) (merC v) = realC (frameL y v)`
(`unitRC (εy) = realC (eR y)`, `unitZC = realC e3`). -/
def DictFrame : Prop :=
  ∀ (ε : ℝ), 0 < ε → ∀ (y : Space), y ∉ Axi.axis → ∀ v : Axi.Merid,
    UnforcedLeray.B0223.frameC (ε • y) (merC v) = UnforcedLeray.B0412.realC (Axi.frameL y v)

/-- **Leaf (scalar)** (source 2683): `liftA (ε y) = √(age ε⁻¹ y)` (both equal `(ε ϱ y)⁻¹`). -/
def DictScalar : Prop :=
  ∀ (ε : ℝ), 0 < ε → ∀ (y : Space), y ∉ Axi.axis →
    UnforcedLeray.B0220.liftA (ε • y) = Real.sqrt (Axi.age ε⁻¹ y)

theorem dictVel_of (hQ : DictQmp) (hA : DictAe) (hC : DictChart) (hF : DictFrame)
    (hS : DictScalar) : DictVel := by
  intro p
  have hP : p.period = 2 * p.ε * p.c := rfl
  refine ⟨Real.sqrt (2 * Real.pi) * p.ε, ?_, ?_⟩
  · exact mul_ne_zero (Real.sqrt_pos.2 (by positivity)).ne' p.ε_pos.ne'
  intro g f hgf
  have h1 := UnforcedLeray.B0223.coeFn_liftVec (P := p.period) p.ε_pos p.c_pos rfl g
  have h2 := hA p.ε p.c p.period p.ε_pos p.c_pos hP g f hgf
  have h3 : ∀ᵐ z ∂(volume : Measure (PSpace p.period)),
      (liftVec (P := p.period) p.ε_pos p.c_pos rfl g : PSpace p.period → SpaceC) z =
        (Real.sqrt (2 * Real.pi) * p.ε)⁻¹ • UnforcedLeray.B0220.liftA z.1 •
          UnforcedLeray.B0223.frameC z.1 (merC (f (cellPt p.c
            (UnforcedLeray.B0220.cellChart p.ε p.c (UnforcedLeray.B0223.toCell p.period z))))) := by
    filter_upwards [h1, h2] with z hz1 hz2
    rw [hz1]
    exact congrArg _ (congrArg _ (congrArg _ hz2))
  have h4 := (hQ p.period p.ε p.ε_pos.ne').ae h3
  have h5 : ∀ᵐ x ∂(volume : Measure (ℝ × Space)), x.2 ∉ Axi.axis := by
    have := (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ))
      (ν := (volume : Measure Space))).ae (p := fun y : Space => y ∉ Axi.axis)
      (by rw [ae_iff]; simpa using Axi.volume_axis)
    exact this
  filter_upwards [h4, h5] with x hx4 hx5
  obtain ⟨τ, y⟩ := x
  simp only at hx4 hx5
  unfold velPhys repX
  simp only
  rw [hx4]
  unfold Axi.Nv
  rw [hC p.ε p.c p.period p.ε_pos p.c_pos hP f y hx5 τ, hF p.ε p.ε_pos y hx5, hS p.ε p.ε_pos y hx5]
  have hr : ∀ (a : ℝ) (v : Space), UnforcedLeray.B0412.realC (a • v) =
      (a : ℂ) • UnforcedLeray.B0412.realC v := by
    intro a v
    ext i
    simp [UnforcedLeray.B0412.realC_apply]
  rw [hr, ← Complex.coe_smul, ← Complex.coe_smul, smul_smul, smul_smul]
  have hk : (Real.sqrt (2 * Real.pi) * p.ε) ≠ 0 :=
    mul_ne_zero (Real.sqrt_pos.2 (by positivity)).ne' p.ε_pos.ne'
  rw [← Complex.ofReal_mul, mul_inv_cancel₀ hk, Complex.ofReal_one, one_mul]

end UnforcedLeray.Short.PartIIIb.NearInst
