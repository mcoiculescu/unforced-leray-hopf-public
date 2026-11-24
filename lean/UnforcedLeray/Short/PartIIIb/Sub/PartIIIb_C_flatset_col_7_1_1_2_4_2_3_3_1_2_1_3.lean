import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_3_1_2_1

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Cyl (Vec2 Plane)

/-- (b), period `c ≥ 1` (source 1650-1656): the scalar estimate `TrainB.smooth_cyl_H2_bound`
(`‖f z‖ₑ ≤ 3 (A+B+C+D)`, four cell `L²` norms of `f, ∂q f, ∂η f, ∂η∂q f`) applied to the two
components of a `Vec2` field: if `0 ≤ B` and the cell-`c` `L²` norms of all coordinate derivatives of
order `≤ 2` are `≤ B`, then `‖f x‖ ≤ 24 B`.  (The words `[]`, `[(1,0)]`, `[(0,1)]`,
`[(0,1),(1,0)]` are used; components are bounded in `L²` by the norm of the `Vec2` field.) -/
def MorreyTwoDerivsLarge : Prop :=
  ∀ (c : ℝ), 1 ≤ c → ∀ (f : Plane → Vec2), UnforcedLeray.Sob.IsCylSmooth c f → ∀ (B : ℝ), 0 ≤ B →
    (∀ v : List Plane, IsCoordWord v → v.length ≤ 2 →
      eLpNorm (UnforcedLeray.Sob.iterD v f) 2 (UnforcedLeray.Cyl.cellμ c) ≤ ENNReal.ofReal B) →
    ∀ x : Plane, ‖f x‖ ≤ 24 * B

/-- Period reduction (source 1650-1656, `c < 1`): for `c > 0` and `N : ℕ`, `1 ≤ N`, a `c`-cylinder
smooth field is `N c`-cylinder smooth, and each coordinate-derivative `L²` norm over the cell of
width `N c` is `≤ √N` times the one over the cell of width `c` (the big cell is `N` translates of the
small one: `Sob.isAddFundamentalDomain_cylCell`, `Sob.lintegral_unfold`, periodicity of
`iterD v f`). -/
def CellPeriodReduction : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (N : ℕ), 1 ≤ N → ∀ (f : Plane → Vec2), UnforcedLeray.Sob.IsCylSmooth c f →
    UnforcedLeray.Sob.IsCylSmooth ((N : ℝ) * c) f ∧
    ∀ v : List Plane,
      eLpNorm (UnforcedLeray.Sob.iterD v f) 2 (UnforcedLeray.Cyl.cellμ ((N : ℝ) * c)) ≤
        ENNReal.ofReal (Real.sqrt N) *
          eLpNorm (UnforcedLeray.Sob.iterD v f) 2 (UnforcedLeray.Cyl.cellμ c)

theorem morreyTwoDerivs_of (h1 : MorreyTwoDerivsLarge) (h2 : CellPeriodReduction) :
    MorreyTwoDerivs := by
  intro c hc
  set N : ℕ := ⌈1 / c⌉₊ with hN
  have hN1 : 1 ≤ N := by
    have : 0 < 1 / c := by positivity
    exact Nat.one_le_iff_ne_zero.mpr (by simpa [hN] using this)
  have hNc : 1 ≤ (N : ℝ) * c := by
    have h : 1 / c ≤ N := Nat.le_ceil _
    have := mul_le_mul_of_nonneg_right h hc.le
    rwa [one_div, inv_mul_cancel₀ hc.ne'] at this
  refine ⟨24 * Real.sqrt N, by positivity, fun f hf B hB hder x => ?_⟩
  obtain ⟨hf', hscale⟩ := h2 c hc N hN1 f hf
  have key := h1 ((N : ℝ) * c) hNc f hf' (Real.sqrt N * B) (by positivity) (fun v hv hvl => by
    calc eLpNorm (UnforcedLeray.Sob.iterD v f) 2 (UnforcedLeray.Cyl.cellμ ((N : ℝ) * c))
        ≤ ENNReal.ofReal (Real.sqrt N) *
            eLpNorm (UnforcedLeray.Sob.iterD v f) 2 (UnforcedLeray.Cyl.cellμ c) := hscale v
      _ ≤ ENNReal.ofReal (Real.sqrt N) * ENNReal.ofReal B := by gcongr; exact hder v hv hvl
      _ = ENNReal.ofReal (Real.sqrt N * B) := by
          rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]) x
  calc ‖f x‖ ≤ 24 * (Real.sqrt N * B) := key
    _ = 24 * Real.sqrt N * B := by ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
