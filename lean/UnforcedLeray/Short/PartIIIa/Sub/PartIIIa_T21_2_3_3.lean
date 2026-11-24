import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_3

/-!
# Part III-a, task `PartIII-a:T21/2/3/3` (`MovingPhiH1`): decomposition

Source of record: `the November 2 reference manuscript`, lines 3044, 3074-3075
(the moving adjoint `Φ = movingPhi ν φ t` is a weak `H¹_{-m,d_t}` function with classical
derivatives).

`movingPhiH1_of` proves `MovingPhiH1 m` from three leaf Props:
* `MpWeakFromSmooth`: a smooth `d`-periodic function has weak cell derivatives equal to its
  classical ones (integration by parts on the cell, periodic boundary terms cancel);
* `MpScaleMemLp`: scaling `y ↦ K f(√a y)` maps `L²(cellMeasure c (-m))` into
  `L²(cellMeasure (c/√a) (-m))` for continuous `f`;
* `MpPdScale`: chain rule `pdCx j (movingPhi ν φ t) = a⁻¹ √a (pdCx j (φ t))(√a ·)`.
Smoothness and periodicity of `movingPhi` are proved here.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **Leaf** (SP 3074-3075): a smooth function, periodic of period `d` in the first variable, has
weak cell derivatives (against `IsCylTest d`) equal to its classical partial derivatives `pdCx`.
Proof: Fubini over the centred cell `[-d/2, d/2) × ℝ`, 1D integration by parts in the direction
`j` (for `j = 0` the boundary terms cancel by periodicity; for `j = 1` the test is compactly
supported in `η`); integrability of `Φ pd ψ`, `pdCx Φ ψ` by continuity on the compact band. -/
def MpWeakFromSmooth : Prop :=
  ∀ (d : ℝ), 0 < d → ∀ Φ : ℝ × ℝ → ℂ, ContDiff ℝ ∞ Φ → (∀ x : ℝ × ℝ, Φ (x.1 + d, x.2) = Φ x) →
    ∀ j : Fin 2, HasWeakCellDerivC d j Φ (pdCx j Φ)

/-- **Leaf** (SP 3044): change of variables `x = √a y` in the weighted `L²` norm. For continuous
`f ∈ L²(cellMeasure c (-m))`, `a > 0`, `K` real, the function `y ↦ K f(√a y)` lies in
`L²(cellMeasure (c/√a) (-m))` (`jb(√a y)` is between `jb(y)` and `a jb(y)`; same bridge as
`h1s_bridge` in `Sub/T21_2_3/H1BySeminorm.lean`). -/
def MpScaleMemLp : Prop :=
  ∀ (m c a : ℝ), 0 < c → 0 < a → ∀ (K : ℝ) (f : ℝ × ℝ → ℂ), Continuous f →
    MemLp f 2 (B0579.cellMeasure c (-m)) →
    MemLp (fun y : ℝ × ℝ => (K : ℂ) * f (Real.sqrt a * y.1, Real.sqrt a * y.2)) 2
      (B0579.cellMeasure (cellLen c a) (-m))

/-- **Leaf** (chain rule): for smooth `φ t`, `a = clockA ν t > 0`,
`pdCx j (movingPhi ν φ t) y = (a⁻¹ √a : ℝ) · pdCx j (φ t) (√a y₁, √a y₂)`. -/
def MpPdScale : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (t : ℝ), 0 ≤ t → ∀ φ : ℝ → ℝ × ℝ → ℂ, ContDiff ℝ ∞ (φ t) →
    ∀ (j : Fin 2) (y : ℝ × ℝ), pdCx j (movingPhi ν φ t) y =
      (((clockA ν t)⁻¹ * Real.sqrt (clockA ν t) : ℝ) : ℂ) *
        pdCx j (φ t) (Real.sqrt (clockA ν t) * y.1, Real.sqrt (clockA ν t) * y.2)

lemma mp_smooth (ν : ℝ) (t : ℝ) (φ : ℝ → ℝ × ℝ → ℂ) (h : ContDiff ℝ ∞ (φ t)) :
    ContDiff ℝ ∞ (movingPhi ν φ t) := by
  unfold movingPhi
  refine contDiff_const.mul (h.comp ?_)
  exact (contDiff_const.mul contDiff_fst).prodMk (contDiff_const.mul contDiff_snd)

lemma mp_periodic (ν c : ℝ) (hc : 0 < c) (t : ℝ) (ht : 0 ≤ t) (hν : 0 < ν)
    (φ : ℝ → ℝ × ℝ → ℂ) (h : ∀ x : ℝ × ℝ, φ t (x.1 + c, x.2) = φ t x) (x : ℝ × ℝ) :
    movingPhi ν φ t (x.1 + cellLen c (clockA ν t), x.2) = movingPhi ν φ t x := by
  have ha : 0 < clockA ν t := by unfold clockA; positivity
  have hs : 0 < Real.sqrt (clockA ν t) := Real.sqrt_pos.mpr ha
  unfold movingPhi cellLen
  have : Real.sqrt (clockA ν t) * (x.1 + c / Real.sqrt (clockA ν t)) =
      Real.sqrt (clockA ν t) * x.1 + c := by field_simp
  simp only
  rw [this]
  exact congrArg _ (h (Real.sqrt (clockA ν t) * x.1, Real.sqrt (clockA ν t) * x.2))

theorem movingPhiH1_of (m : ℝ) (h1 : MpWeakFromSmooth) (h2 : MpScaleMemLp) (h3 : MpPdScale) :
    MovingPhiH1 m := by
  intro ν hν tr t s ht hts g φ hφ
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have ha : 0 < clockA ν t := by unfold clockA; positivity
  have htI : t ∈ Icc t s := ⟨le_rfl, hts.le⟩
  have htI' : t ∈ Ico t s := ⟨le_rfl, hts⟩
  have hsm := hφ.smooth t htI'
  have hd : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν t) := by
    unfold cellLen; exact div_pos hc (Real.sqrt_pos.mpr ha)
  have hper := mp_periodic ν _ hc t ht hν φ (hφ.periodic t htI')
  refine ⟨fun j => h1 _ hd _ (mp_smooth ν t φ hsm) hper j, ?_, fun j => ?_⟩
  · have := h2 m _ (clockA ν t) hc ha ((clockA ν t)⁻¹) (φ t) hsm.continuous (hφ.memX t htI)
    exact this
  · have hpd : True := trivial
    have hcont : Continuous (pdCx j (φ t)) := by
      have : ContDiff ℝ ∞ (fun y => fderiv ℝ (φ t) y (B0579.dir j)) :=
        (hsm.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
      exact this.continuous
    have := h2 m _ (clockA ν t) hc ha ((clockA ν t)⁻¹ * Real.sqrt (clockA ν t)) _ hcont
      (hφ.memH1 t htI' j)
    have e : pdCx j (movingPhi ν φ t) = fun y : ℝ × ℝ =>
        ((((clockA ν t)⁻¹ * Real.sqrt (clockA ν t) : ℝ)) : ℂ) *
          pdCx j (φ t) (Real.sqrt (clockA ν t) * y.1, Real.sqrt (clockA ν t) * y.2) :=
      funext fun y => h3 ν hν t ht φ hsm j y
    rw [e]
    exact this

end UnforcedLeray.Short.IIIa
