import UnforcedLeray.Short.PartIIa.Calc.BlockA2Calc

/-!
# Part II-a, block `A₂`, task `PartII-a:R02/12/2`: the heat operator is additive on smooth families

Source: `the November 2 reference manuscript`, lines 1284-1285.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.Jet.A2

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0188 UnforcedLeray.B0190

/-! ### Calculus on `{s > 0}` (helpers, prefix `ha1_`) -/

theorem ha1_fderiv_add {f g : ProfilePoint → ℝ} {x : ProfilePoint}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    fderiv ℝ (f + g) x = fderiv ℝ f x + fderiv ℝ g x :=
  fderiv_add hf hg

theorem ha1_fderiv_sub {f g : ProfilePoint → ℝ} {x : ProfilePoint}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    fderiv ℝ (f - g) x = fderiv ℝ f x - fderiv ℝ g x :=
  fderiv_sub hf hg

theorem ha1_diff {f : ProfilePoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f {y : ProfilePoint | 0 < y.2.2}) {x : ProfilePoint}
    (hx : x ∈ {y : ProfilePoint | 0 < y.2.2}) : DifferentiableAt ℝ f x :=
  (hf.contDiffAt (UnforcedLeray.Short.PartIIa.isOpen_late.mem_nhds hx)).differentiableAt (by simp)

theorem ha1_partialAge_add {f g : ProfilePoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f {y : ProfilePoint | 0 < y.2.2})
    (hg : ContDiffOn ℝ ∞ g {y : ProfilePoint | 0 < y.2.2})
    {x : ProfilePoint} (hx : x ∈ {y : ProfilePoint | 0 < y.2.2}) :
    partialAge (f + g) x = partialAge f x + partialAge g x := by
  show fderiv ℝ (f + g) x esDir = fderiv ℝ f x esDir + fderiv ℝ g x esDir
  rw [ha1_fderiv_add (ha1_diff hf hx) (ha1_diff hg hx), ContinuousLinearMap.add_apply]

theorem ha1_partialAge_sub {f g : ProfilePoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f {y : ProfilePoint | 0 < y.2.2})
    (hg : ContDiffOn ℝ ∞ g {y : ProfilePoint | 0 < y.2.2})
    {x : ProfilePoint} (hx : x ∈ {y : ProfilePoint | 0 < y.2.2}) :
    partialAge (f - g) x = partialAge f x - partialAge g x := by
  show fderiv ℝ (f - g) x esDir = fderiv ℝ f x esDir - fderiv ℝ g x esDir
  rw [ha1_fderiv_sub (ha1_diff hf hx) (ha1_diff hg hx), ContinuousLinearMap.sub_apply]

theorem ha1_partialEta_add_ev {f g : ProfilePoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f {y : ProfilePoint | 0 < y.2.2})
    (hg : ContDiffOn ℝ ∞ g {y : ProfilePoint | 0 < y.2.2})
    {x : ProfilePoint} (hx : x ∈ {y : ProfilePoint | 0 < y.2.2}) :
    partialEta (f + g) =ᶠ[𝓝 x] partialEta f + partialEta g := by
  refine Filter.eventuallyEq_of_mem (UnforcedLeray.Short.PartIIa.isOpen_late.mem_nhds hx)
    (fun y hy => ?_)
  show fderiv ℝ (f + g) y eηDir = fderiv ℝ f y eηDir + fderiv ℝ g y eηDir
  rw [ha1_fderiv_add (ha1_diff hf hy) (ha1_diff hg hy), ContinuousLinearMap.add_apply]

theorem ha1_partialEta_sub_ev {f g : ProfilePoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f {y : ProfilePoint | 0 < y.2.2})
    (hg : ContDiffOn ℝ ∞ g {y : ProfilePoint | 0 < y.2.2})
    {x : ProfilePoint} (hx : x ∈ {y : ProfilePoint | 0 < y.2.2}) :
    partialEta (f - g) =ᶠ[𝓝 x] partialEta f - partialEta g := by
  refine Filter.eventuallyEq_of_mem (UnforcedLeray.Short.PartIIa.isOpen_late.mem_nhds hx)
    (fun y hy => ?_)
  show fderiv ℝ (f - g) y eηDir = fderiv ℝ f y eηDir - fderiv ℝ g y eηDir
  rw [ha1_fderiv_sub (ha1_diff hf hy) (ha1_diff hg hy), ContinuousLinearMap.sub_apply]

theorem ha1_partialEta_partialEta_add {f g : ProfilePoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f {y : ProfilePoint | 0 < y.2.2})
    (hg : ContDiffOn ℝ ∞ g {y : ProfilePoint | 0 < y.2.2})
    {x : ProfilePoint} (hx : x ∈ {y : ProfilePoint | 0 < y.2.2}) :
    partialEta (partialEta (f + g)) x = partialEta (partialEta f) x + partialEta (partialEta g) x := by
  have hd1 : DifferentiableAt ℝ (partialEta f) x :=
    ha1_diff (UnforcedLeray.Short.PartIIa.contDiffOn_fderiv_apply hf eηDir) hx
  have hd2 : DifferentiableAt ℝ (partialEta g) x :=
    ha1_diff (UnforcedLeray.Short.PartIIa.contDiffOn_fderiv_apply hg eηDir) hx
  show fderiv ℝ (partialEta (f + g)) x eηDir
    = fderiv ℝ (partialEta f) x eηDir + fderiv ℝ (partialEta g) x eηDir
  rw [(ha1_partialEta_add_ev hf hg hx).fderiv_eq, ha1_fderiv_add hd1 hd2,
    ContinuousLinearMap.add_apply]

theorem ha1_partialEta_partialEta_sub {f g : ProfilePoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f {y : ProfilePoint | 0 < y.2.2})
    (hg : ContDiffOn ℝ ∞ g {y : ProfilePoint | 0 < y.2.2})
    {x : ProfilePoint} (hx : x ∈ {y : ProfilePoint | 0 < y.2.2}) :
    partialEta (partialEta (f - g)) x = partialEta (partialEta f) x - partialEta (partialEta g) x := by
  have hd1 : DifferentiableAt ℝ (partialEta f) x :=
    ha1_diff (UnforcedLeray.Short.PartIIa.contDiffOn_fderiv_apply hf eηDir) hx
  have hd2 : DifferentiableAt ℝ (partialEta g) x :=
    ha1_diff (UnforcedLeray.Short.PartIIa.contDiffOn_fderiv_apply hg eηDir) hx
  show fderiv ℝ (partialEta (f - g)) x eηDir
    = fderiv ℝ (partialEta f) x eηDir - fderiv ℝ (partialEta g) x eηDir
  rw [(ha1_partialEta_sub_ev hf hg hx).fderiv_eq, ha1_fderiv_sub hd1 hd2,
    ContinuousLinearMap.sub_apply]

/-- The heat operator, pointwise. -/
theorem ha1_heatOp_pt (X : Fam) (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (x : ProfilePoint) :
    heatOp X ν c tr x = partialAge (X ν c tr) x - ν * partialEta (partialEta (X ν c tr)) x :=
  rfl

/-! ### The statement -/

/-- **The heat operator is additive on smooth families** (task `PartII-a:R02/12/2`). -/
theorem heatOpLin : UnforcedLeray.Short.PartIIa.Jet.A2.HeatOpLin := by
  intro F G hF hG
  constructor
  · intro ν c hν hc tr htr x hx
    have hFt := hF ν c hν hc tr htr
    have hGt := hG ν c hν hc tr htr
    show partialAge (F ν c tr + G ν c tr) x - ν * partialEta (partialEta (F ν c tr + G ν c tr)) x
      = (partialAge (F ν c tr) x - ν * partialEta (partialEta (F ν c tr)) x)
        + (partialAge (G ν c tr) x - ν * partialEta (partialEta (G ν c tr)) x)
    rw [ha1_partialAge_add hFt hGt hx, ha1_partialEta_partialEta_add hFt hGt hx]
    ring
  · intro ν c hν hc tr htr x hx
    have hFt := hF ν c hν hc tr htr
    have hGt := hG ν c hν hc tr htr
    show partialAge (F ν c tr - G ν c tr) x - ν * partialEta (partialEta (F ν c tr - G ν c tr)) x
      = (partialAge (F ν c tr) x - ν * partialEta (partialEta (F ν c tr)) x)
        - (partialAge (G ν c tr) x - ν * partialEta (partialEta (G ν c tr)) x)
    rw [ha1_partialAge_sub hFt hGt hx, ha1_partialEta_partialEta_sub hFt hGt hx]
    ring

end UnforcedLeray.Short.PartIIa.Jet.A2
