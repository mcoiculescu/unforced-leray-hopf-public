import UnforcedLeray.Lib.Train.PeriodizedVortex
import UnforcedLeray.Units.B0147

/-!
# Bounds for the periodized heat vortex, transported to `Vec` (INF16 T2, output O3 bounds)


target T2 ("the bounds themselves are INF27 G7"). Blueprint unit **B0147** (`eq:st18-t00145`,
`paper/main.tex` lines 2217–2234): for `1 ≤ a ≤ c²` and every fixed `j`,
`‖D^jV_c‖_∞ ≤ C_j a^{-(3+j)/2}`, `‖V_c‖₂ ≤ C a^{-1}`, `‖D^jQ_c‖₂ ≤ C_j a^{-(5+j)/2} e^{-b_jc²/a}`,
with any fixed transverse weight in units of `√a`.

These bounds are proved in the compiled unit `Units/B0147.lean` (`unit_B0147`) for the
`ℝ × ℝ`-valued fields of unit B0146; this file restates them for `Vc`, `Qc` of
`PeriodizedVortex.lean` through `Vc_eq`, `Qc_fun_eq`. Conventions are B0147's:
`D^j` is every word of `j` classical partials (`B0151.derivWord`, proved genuine there), the
weight is `(1 + η²/a)^m`, and cell norms are `eLpNorm · 2 (B0151.cellMeasure c)` on
`(0, c] × ℝ` in `ℝ≥0∞`, together with `MemLp` (no junk integrals). Hypotheses: `0 < c`,
`1 ≤ a ≤ c²` with `a = width ν s`; constants depend only on `j` and `m`.

Main declaration: `Vc_bounds`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UnforcedLeray.Train

open UnforcedLeray.Cyl (Plane)

theorem Vc_comp_eq (ν c s : ℝ) (k : Fin 2) :
    (fun x => Vc ν c s x k) = fun x => B0146.vcomp (B0146.periodicVelocity ν c s x) k :=
  funext fun x => by rw [Vc_eq, toVec_apply_eq_vcomp]

/-- **The bounds `eq:st18-t00145` for `V_c` and `Q_c`** (tex lines 2217–2234), with the
transverse weight `(1 + η²/a)^m`; transported from `B0147.unit_B0147`. -/
theorem Vc_bounds (j m : ℕ) :
    ∃ C b : ℝ, 0 ≤ C ∧ 0 < b ∧
      ∀ ν c s : ℝ, 0 < c → 1 ≤ width ν s → width ν s ≤ c ^ 2 →
        (∀ w : List Bool, w.length = j → ∀ (k : Fin 2) (z : Plane),
          (1 + z.2 ^ 2 / width ν s) ^ m * |B0151.derivWord w (fun x => Vc ν c s x k) z| ≤
            C * width ν s ^ (-(3 + (j : ℝ)) / 2)) ∧
        (∀ k : Fin 2,
          MemLp (fun z : Plane => (1 + z.2 ^ 2 / width ν s) ^ m * Vc ν c s z k) 2
            (B0151.cellMeasure c) ∧
          eLpNorm (fun z : Plane => (1 + z.2 ^ 2 / width ν s) ^ m * Vc ν c s z k) 2
            (B0151.cellMeasure c) ≤ ENNReal.ofReal (C * (width ν s)⁻¹)) ∧
        (∀ w : List Bool, w.length = j → ∀ k l : Fin 2,
          MemLp (fun z : Plane => (1 + z.2 ^ 2 / width ν s) ^ m *
            B0151.derivWord w (fun x => Qc ν c s x k l) z) 2 (B0151.cellMeasure c) ∧
          eLpNorm (fun z : Plane => (1 + z.2 ^ 2 / width ν s) ^ m *
            B0151.derivWord w (fun x => Qc ν c s x k l) z) 2 (B0151.cellMeasure c) ≤
              ENNReal.ofReal (C * width ν s ^ (-(5 + (j : ℝ)) / 2) *
                Real.exp (-(b * c ^ 2 / width ν s)))) := by
  obtain ⟨C, b, hC, hb, h, -, -⟩ := B0147.unit_B0147 j m
  refine ⟨C, b, hC, hb, fun ν c s hc ha1 hac => ?_⟩
  obtain ⟨h1, h2, h3⟩ := h ν c s hc ha1 hac
  refine ⟨fun w hw k z => ?_, fun k => ?_, fun w hw k l => ?_⟩
  · rw [Vc_comp_eq]; exact h1 w hw k z
  · have e : (fun z : Plane => (1 + z.2 ^ 2 / width ν s) ^ m * Vc ν c s z k) =
        fun z => (1 + z.2 ^ 2 / B0113.heatWidth ν s) ^ m *
          B0146.vcomp (B0146.periodicVelocity ν c s z) k :=
      funext fun z => by rw [Vc_eq, toVec_apply_eq_vcomp]; rfl
    rw [e]; exact h2 k
  · rw [Qc_fun_eq]; exact h3 w hw k l

end UnforcedLeray.Train
