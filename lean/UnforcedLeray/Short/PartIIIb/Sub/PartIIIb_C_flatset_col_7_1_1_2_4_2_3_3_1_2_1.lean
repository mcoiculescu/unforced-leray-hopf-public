import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_3_1_2

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Cyl (Vec2 Plane)

/-- Coordinate direction words: lists of the two unit vectors of the plane. -/
def IsCoordWord (w : List Plane) : Prop := ∀ a ∈ w, a = ((1 : ℝ), (0 : ℝ)) ∨ a = ((0 : ℝ), (1 : ℝ))

/-- (d) **Finite-dimensional comparison of `iteratedFDeriv` with coordinate words**
(source 1684-1689, norm of the `j`-th derivative bounded by its coordinate components).
For each `m` there is `K ≥ 0` such that for smooth `u : Plane → Vec2`, `j ≤ m` and `x`:
if all coordinate-word derivatives `iterD w u x` with `|w| = j` have norm `≤ B`, then
`‖iteratedFDeriv ℝ j u x‖ ≤ K * B`. -/
def IteratedFDerivByWords : Prop :=
  ∀ m : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ (u : Plane → Vec2), ContDiff ℝ ∞ u → ∀ (j : ℕ), j ≤ m → ∀ x : Plane,
    ∀ B : ℝ, (∀ w : List Plane, IsCoordWord w → w.length = j →
      ‖UnforcedLeray.Sob.iterD w u x‖ ≤ B) → ‖iteratedFDeriv ℝ j u x‖ ≤ K * B

/-- (a)+(c) **Sobolev norm dominates the cell `L²` norms of coordinate words**
(source 1650-1656; for `c < 1` by the period reduction `N c ≥ 1`).  With `k = m + 2`:
`‖∂^v ∂^w u‖_{L²(cell c)} ≤ C ‖u‖_{H^k}` for coordinate words `|w| ≤ m`, `|v| ≤ 2`. -/
def CellL2ByNorm : Prop :=
  ∀ (c : ℝ) (hc : 0 < c) (m : ℕ), ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (u : Plane → Vec2)
    (hu : UnforcedLeray.Sob.IsCylSmooth c u) (w v : List Plane), IsCoordWord w → w.length ≤ m →
      IsCoordWord v → v.length ≤ 2 →
      eLpNorm (UnforcedLeray.Sob.iterD v (UnforcedLeray.Sob.iterD w u)) 2
          (UnforcedLeray.Cyl.cellμ c) ≤
        ENNReal.ofReal (C * ‖UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := Vec2)
          (k := k) (p := 2) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc u hu‖)

/-- (b) **Two-derivative Morrey sup bound** (source 1650-1656), any `c > 0` (for `c < 1` by period
reduction): a smooth periodic `Vec2` field is bounded in sup norm by the cell `L²` norms of its
coordinate derivatives of order `≤ 2`: if `0 ≤ B` and all of these are `≤ B` then `‖f x‖ ≤ C B`.
(The hypothesis `0 ≤ B` is needed: `ENNReal.ofReal` of a negative number is `0`.) -/
def MorreyTwoDerivs : Prop :=
  ∀ (c : ℝ) (_hc : 0 < c), ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Plane → Vec2)
    (_hf : UnforcedLeray.Sob.IsCylSmooth c f) (B : ℝ), 0 ≤ B →
    (∀ v : List Plane, IsCoordWord v → v.length ≤ 2 →
      eLpNorm (UnforcedLeray.Sob.iterD v f) 2 (UnforcedLeray.Cyl.cellμ c) ≤ ENNReal.ofReal B) →
    ∀ x : Plane, ‖f x‖ ≤ C * B

theorem smoothSupK_of (h1 : IteratedFDerivByWords) (h2 : CellL2ByNorm) (h3 : MorreyTwoDerivs) :
    SmoothSupK := by
  intro c hc m
  obtain ⟨K, hK, hKb⟩ := h1 m
  obtain ⟨k, C2, hC2, h2b⟩ := h2 c hc m
  obtain ⟨C3, hC3, h3b⟩ := h3 c hc
  refine ⟨k, K * (C3 * C2), mul_nonneg hK (mul_nonneg hC3 hC2), fun u hu j hj x => ?_⟩
  set N := ‖UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := Vec2)
    (k := k) (p := 2) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc u hu‖ with hN
  have key : ‖iteratedFDeriv ℝ j u x‖ ≤ K * (C3 * (C2 * N)) := by
    refine hKb u hu.smooth j hj x (C3 * (C2 * N)) (fun w hw hwl => ?_)
    exact h3b (UnforcedLeray.Sob.iterD w u) (hu.iterD w) (C2 * N) (mul_nonneg hC2 (norm_nonneg _))
      (fun v hv hvl => h2b u hu w v hw (hwl ▸ hj) hv hvl) x
  calc ‖iteratedFDeriv ℝ j u x‖ ≤ K * (C3 * (C2 * N)) := key
    _ = K * (C3 * C2) * N := by ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
