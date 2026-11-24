import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive.Leaf
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.ZRegular.Src
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L3
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L4

/-!
# Bridge (1): the old physical source as a thin source (helper for `GeomX.PhasePrimitive`)

Source `the November 2 reference manuscript`
lines 2666-2687 (ring chart `s = R²/ϱ²`, `q = R log(ϱ/R) + Rτ/2`, `η = Rz₃/ϱ`; lift `𝒩_TT = sT`),
5400-5427; SP 3746-3751 (`T(z,τ) = F(z'/R, z₃, q_ε(|z'|/R, τ))`).

With `x' = εz'`, `Y = z₃`, `s = |x'|⁻²`, `η = Y√s` and the cell reduction `redQ` of the phase, the
old source `oldPhys ε⁻¹ c g` is **exactly** `IIIa.thinSource ε (plift c g)`, where
`plift c g x' Y q = Q(x') (s • nsSym g(s, redQ q, η)) Q(x')ᵀ`.  The cut version `cutLift` (zero for
`|x'| > ρ_o`) is the thin source of `oldCutSrc`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace PhasePrim

/-- The reduction of a phase into the cell `[-c/2, c/2)` (as in `NearInst.chartOf`). -/
def redQ (c q : ℝ) : ℝ := q - c * ⌊q / c + 1 / 2⌋

/-- The cylindrical frame at the planar point `x'`. -/
def plFrame (x' : ℝ × ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  NearInst.cylFrame (WithLp.toLp 2 ![x'.1, x'.2, 0])

/-- The age `s = |x'|⁻²` of the planar point `x'`. -/
def plS (x' : ℝ × ℝ) : ℝ := (x'.1 ^ 2 + x'.2 ^ 2)⁻¹

/-- The planar lift `F(x',Y,q) = Q(x') (s • nsSym g(s, redQ q, Y√s)) Q(x')ᵀ`, `s = |x'|⁻²`. -/
def plift (c : ℝ) (g : Chart → Ten3) (x' : ℝ × ℝ) (Y q : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  plFrame x' * (plS x' • NearInst.nsSym (g (plS x', (redQ c q, Y * Real.sqrt (plS x'))))) *
    (plFrame x').transpose

/-- The planar lift cut off outside the old disk `|x'| ≤ ρ_o`. -/
def cutLift (c ρo : ℝ) (g : Chart → Ten3) : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ :=
  fun x' Y q => if Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) ≤ ρo then plift c g x' Y q else 0

theorem sqrt_eps (ε : ℝ) (hε : 0 ≤ ε) (a b : ℝ) :
    Real.sqrt ((ε * a) ^ 2 + (ε * b) ^ 2) = ε * Real.sqrt (a ^ 2 + b ^ 2) := by
  rw [show (ε * a) ^ 2 + (ε * b) ^ 2 = ε ^ 2 * (a ^ 2 + b ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg ε), Real.sqrt_sq hε]

theorem hRad_pl (a b c : ℝ) : NearInst.hRad (WithLp.toLp 2 ![a, b, c]) = Real.sqrt (a ^ 2 + b ^ 2) := by
  simp [NearInst.hRad]

theorem plFrame_eps (ε : ℝ) (hε : 0 < ε) (z : Space) :
    plFrame (ε * z 0, ε * z 1) = NearInst.cylFrame z := by
  unfold plFrame NearInst.cylFrame
  rw [hRad_pl, sqrt_eps ε hε.le]
  have hz : NearInst.hRad z = Real.sqrt (z 0 ^ 2 + z 1 ^ 2) := rfl
  rw [← hz]
  simp only [PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [mul_div_mul_left _ _ hε.ne', mul_div_mul_left _ _ hε.ne']

theorem plS_eps (ε : ℝ) (z : Space) :
    plS (ε * z 0, ε * z 1) = ε⁻¹ ^ 2 / NearInst.hRad z ^ 2 := by
  unfold plS NearInst.hRad
  rw [Real.sq_sqrt (by positivity), div_eq_mul_inv, inv_pow, ← mul_inv]
  congr 1
  ring

theorem chartOf_eps (ε c : ℝ) (hε : 0 < ε) (z : Space) (τ : ℝ) :
    NearInst.chartOf ε⁻¹ c z τ = (plS (ε * z 0, ε * z 1),
      (redQ c (ε⁻¹ * Real.log (ε * Real.sqrt (z 0 ^ 2 + z 1 ^ 2)) + τ / (2 * ε)),
        z 2 * Real.sqrt (plS (ε * z 0, ε * z 1)))) := by
  have hz : NearInst.hRad z = Real.sqrt (z 0 ^ 2 + z 1 ^ 2) := rfl
  have hX : ε⁻¹ * Real.log (NearInst.hRad z / ε⁻¹) + ε⁻¹ * τ / 2 =
      ε⁻¹ * Real.log (ε * Real.sqrt (z 0 ^ 2 + z 1 ^ 2)) + τ / (2 * ε) := by
    rw [div_inv_eq_mul, hz, mul_comm (Real.sqrt _) ε]
    field_simp
  have hη : ε⁻¹ * z 2 / NearInst.hRad z = z 2 * Real.sqrt (plS (ε * z 0, ε * z 1)) := by
    unfold plS
    rw [Real.sqrt_inv, sqrt_eps ε hε.le, hz, mul_inv]
    ring
  unfold NearInst.chartOf redQ
  rw [hX, hη, plS_eps]

theorem plift_eps (ε c : ℝ) (hε : 0 < ε) (g : Chart → Ten3) (τ : ℝ) (z : Space) :
    plift c g (ε * z 0, ε * z 1) (z 2)
        (ε⁻¹ * Real.log (ε * Real.sqrt (z 0 ^ 2 + z 1 ^ 2)) + τ / (2 * ε)) =
      oldPhys ε⁻¹ c g τ z := by
  have hp := (chartOf_eps ε c hε z τ).symm
  have hs : plS (ε * z 0, ε * z 1) = (NearInst.chartOf ε⁻¹ c z τ).1 := by
    rw [chartOf_eps ε c hε z τ]
  unfold plift
  rw [hp, hs, plFrame_eps ε hε z]
  rfl

/-- **Bridge (1)**: the cut planar lift is the thin source of the cut old source. -/
theorem thinSource_cutLift (ε c ρo : ℝ) (hε : 0 < ε) (g : Chart → Ten3) (τ : ℝ) (z : Space) :
    IIIa.thinSource ε (cutLift c ρo g) τ z = oldCutSrc ε⁻¹ c (ε⁻¹ * ρo) g τ z := by
  unfold IIIa.thinSource cutLift oldCutSrc
  dsimp only
  rw [sqrt_eps ε hε.le]
  have hz : NearInst.hRad z = Real.sqrt (z 0 ^ 2 + z 1 ^ 2) := rfl
  have hiff : ε * Real.sqrt (z 0 ^ 2 + z 1 ^ 2) ≤ ρo ↔ NearInst.hRad z ≤ ε⁻¹ * ρo := by
    rw [hz, le_inv_mul_iff₀ hε]
  by_cases h : ε * Real.sqrt (z 0 ^ 2 + z 1 ^ 2) ≤ ρo
  · rw [if_pos h, if_pos (hiff.1 h), plift_eps ε c hε g τ z]
  · rw [if_neg h, if_neg (fun h' => h (hiff.2 h'))]

theorem redQ_add (c : ℝ) (hc : c ≠ 0) (q : ℝ) : redQ c (q + c) = redQ c q := by
  unfold redQ
  have : (q + c) / c + 1 / 2 = (q / c + 1 / 2) + 1 := by
    field_simp
    ring
  rw [this, Int.floor_add_one]
  push_cast
  ring

theorem cutLift_periodic (c ρo : ℝ) (hc : c ≠ 0) (g : Chart → Ten3) (x' : ℝ × ℝ) (Y q : ℝ) :
    cutLift c ρo g x' Y (q + c) = cutLift c ρo g x' Y q := by
  unfold cutLift plift
  rw [redQ_add c hc]

theorem cutLift_support (c ρo : ℝ) (g : Chart → Ten3) (x' : ℝ × ℝ) (Y q : ℝ)
    (h : ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2)) : cutLift c ρo g x' Y q = 0 := by
  unfold cutLift
  rw [if_neg (not_le.2 h)]

/-- `cutLift` at `(x',Y,q)` is the cut old source at unit scale. -/
theorem cutLift_eq_one (c ρo : ℝ) (g : Chart → Ten3) (x' : ℝ × ℝ) (Y q : ℝ) :
    cutLift c ρo g x' Y q = oldCutSrc 1⁻¹ c (1⁻¹ * ρo) g
      (2 * (q - Real.log (Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2)))) (WithLp.toLp 2 ![x'.1, x'.2, Y]) := by
  rw [← thinSource_cutLift 1 c ρo one_pos g]
  unfold IIIa.thinSource
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, one_mul, inv_one]
  congr 1
  ring

theorem cutLift_measurable (c ρo : ℝ) (g : Chart → Ten3) (hg : Measurable g) (i j : Fin 3) :
    Measurable fun w : (ℝ × ℝ) × ℝ × ℝ => cutLift c ρo g w.1 w.2.1 w.2.2 i j := by
  have h1 := oldCutMeasurable 1⁻¹ c (1⁻¹ * ρo) g hg i j
  have hτ : Measurable fun w : (ℝ × ℝ) × ℝ × ℝ =>
      2 * (w.2.2 - Real.log (Real.sqrt (w.1.1 ^ 2 + w.1.2 ^ 2))) := by
    fun_prop
  have hz : Measurable fun w : (ℝ × ℝ) × ℝ × ℝ =>
      (WithLp.toLp 2 ![w.1.1, w.1.2, w.2.1] : Space) := by
    have hv : Measurable fun w : (ℝ × ℝ) × ℝ × ℝ => (![w.1.1, w.1.2, w.2.1] : Fin 3 → ℝ) := by
      refine measurable_pi_lambda _ fun k => ?_
      fin_cases k <;> simp <;> fun_prop
    exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp hv
  have h2 := h1.comp (hτ.prodMk hz)
  have e : (fun w : (ℝ × ℝ) × ℝ × ℝ => cutLift c ρo g w.1 w.2.1 w.2.2 i j) =
      (fun p : ℝ × Space => oldCutSrc 1⁻¹ c (1⁻¹ * ρo) g p.1 p.2 i j) ∘
        (fun w : (ℝ × ℝ) × ℝ × ℝ => (2 * (w.2.2 - Real.log (Real.sqrt (w.1.1 ^ 2 + w.1.2 ^ 2))),
          (WithLp.toLp 2 ![w.1.1, w.1.2, w.2.1] : Space))) := by
    funext w
    simp only [Function.comp_apply]
    rw [cutLift_eq_one]
  rw [e]
  exact h2

end PhasePrim

end UnforcedLeray.Short.PartIIIb.Concrete
