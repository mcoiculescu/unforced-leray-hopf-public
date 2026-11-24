import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_3_1_dec

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Cyl (Vec2 Plane)

/-- **Smooth-field Morrey bound** (source 1684-1689; `H^{m+2}(cell) ⊂ C^m` in dimension 2 on the
periodic strip).  For `c > 0` and `m` there are `k` (e.g. `m + 2`) and `C` such that every smooth
`c`-periodic field `u` (vanishing for `|η|` large) has `‖D^j u (x)‖ ≤ C ‖u‖_{H^k(cell)}` for all
`j ≤ m`, all `x`; `‖u‖_{H^k}` is the norm of the Sobolev element `W.ofCylSmooth u`. -/
def SmoothSupK : Prop :=
  ∀ (c : ℝ) (hc : 0 < c) (m : ℕ), ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (u : Plane → Vec2)
    (hu : UnforcedLeray.Sob.IsCylSmooth c u) (j : ℕ), j ≤ m → ∀ x : Plane,
      ‖iteratedFDeriv ℝ j u x‖ ≤ C * ‖UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := Vec2)
        (k := k) (p := 2) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc u hu‖

/-- **Extension from smooth fields to `H^k` by density** (the Banach-space completion argument):
if the `C^m` sup-bounds hold on smooth periodic fields with constant `C` against the `H^k` norm,
then every `y ∈ H^k(cell; ℝ²)` has a `C^m`, `c`-periodic representative `z` with
`sup ‖z‖ ≤ C ‖y‖`.  Route: `Sob.W.exists_seq_cylSmooth` gives smooth `u_n` with `ofCylSmooth u_n → y`;
the bound applied to `u_n - u_p` makes all derivatives of order `≤ m` uniformly Cauchy; the uniform
limit `z` is `C^m` and periodic, and `z = value y` a.e. on the cell by an `L²`-a.e. subsequence
(as in `TrainB.exists_scalarH2_bcf_representative`, `Lib/TrainB/WeakEmbedding.lean:599`). -/
def ExtendFromSmooth : Prop :=
  ∀ (c : ℝ) (hc : 0 < c) (m k : ℕ) (C : ℝ), 0 ≤ C →
    (∀ (u : Plane → Vec2) (hu : UnforcedLeray.Sob.IsCylSmooth c u) (j : ℕ), j ≤ m → ∀ x : Plane,
      ‖iteratedFDeriv ℝ j u x‖ ≤ C * ‖UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := Vec2)
        (k := k) (p := 2) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc u hu‖) →
    ∀ y : UnforcedLeray.Cyl.H ℝ Vec2 c 0 k,
      ∃ z : Plane → Vec2, ContDiff ℝ m z ∧ (∀ x : ℝ × ℝ, z (x.1 + c, x.2) = z x) ∧
        (∀ x, ‖z x‖ ≤ C * ‖y‖) ∧
        z =ᵐ[UnforcedLeray.Cyl.cellμ c]
          ((UnforcedLeray.Sob.W.value _ _ _ _ _ _ y : Plane → Vec2))

theorem cylEmbedK_of (h1 : SmoothSupK) (h2 : ExtendFromSmooth) : CylEmbedK := by
  intro c hc m
  obtain ⟨k, C, hC, hb⟩ := h1 c hc m
  refine ⟨k, C, fun y => ?_⟩
  exact h2 c hc m k C hC (fun u hu j hj x => hb u hu j hj x) y

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
