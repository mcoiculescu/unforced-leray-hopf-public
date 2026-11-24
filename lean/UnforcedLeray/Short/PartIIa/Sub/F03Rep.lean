import UnforcedLeray.Units.B0424.Chart
import UnforcedLeray.Units.B0424.Tests
import UnforcedLeray.Lib.FreeStressCouplings.ProdLp

/-!
# B0424, part 4: pointwise representatives and the window integrals (REPAIRED COPY)

Copy of `Units/B0424/Rep.lean` (which currently fails to compile at `lintegral_rep`, line 110) in


Blueprint unit B0424 (`eq:free-stress-13`, `-14`, `-15`), `paper/main.tex` lines 7479–7517.
The functions `v(t, x) = e^{-t/2} w(τ₀ + t, e^{-t/2} x)` and `g` of tex 7485–7488 are
pointwise formulas in `w ∈ Y_q`. They need a jointly measurable representative of `w` on
`ℝ × ℝ³` (`IsRep`), which exists by the Fubini isometry `L^q(ℝ/Pℤ × ℝ³) ≃ Y_q`
(`exists_isRep`, from `Lib/FreeStressCouplings/ProdLp.lean`); any two representatives agree
almost everywhere.

* `vfun τ₀ W (t, x) = e^{-t/2} W(τ₀ + t, e^{-t/2} x)` (tex 7485–7486).
* `lintegral_vfun`: `∫ m(t) |v|^q dt dx = ∫ m(t) e^{3t/2} e^{-qt/2} ‖w(τ₀ + t)‖_q^q dt` (the
  Jacobian `dx = e^{3t/2} dy` of tex 7502), and `lintegral_window_lt_top`: the window integrals
  of `‖w(τ)‖_q^q` are finite. Hence `v` is in `L^q` on every slab `[a, b] × ℝ³`
  (`isLocLq_vfun`), and `v` times a test is integrable (`IsLocLq.integrable_mul`).
* `integral_vfun_mul` (**unfolding**): `∫ v_i Ψ dt dx = ∫ (∫ w(τ)_i (y) e^t Ψ(t, e^{t/2} y) dy) dτ`,
  `t = τ - τ₀`, which is how the pairings of (13) are pairings of `w` with the phase test of
  `Calc.lean`.

Status: infrastructure for `Units/B0424.lean`. Theorem A is not proved in Lean.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa.Rep

open UnforcedLeray.B0424 UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace UnforcedLeray.Parabolic

variable {P : ℝ} [hP : Fact (0 < P)] {q : ℝ≥0∞} [hq1 : Fact (1 ≤ q)]

/-! ### Jointly measurable representatives -/

/-- `W` is a jointly measurable representative of `w ∈ Y_q` on `ℝ × ℝ³`: for a.e. phase
`τ ∈ ℝ`, `W(τ, ·) = w(τ mod P)` a.e. on `ℝ³`. -/
structure IsRep (w : Yq P q) (W : ℝ × Space → CVec3) : Prop where
  meas : StronglyMeasurable W
  slice : ∀ᵐ τ : ℝ, (fun y => W (τ, y)) =ᵐ[volume] (w (τ : AddCircle P) : Space → CVec3)

/-- Every `w ∈ Y_q`, `q < ∞`, has a jointly measurable representative. -/
theorem exists_isRep (hq : q ≠ ⊤) (w : Yq P q) : ∃ W, IsRep w W := by
  have : Fact (q ≠ ⊤) := ⟨hq⟩
  set G := (FreeStress.prodLpEquiv (ν := AddCircle.haarAddCircle (T := P))
    (μ := (volume : Measure Space)) (F := CVec3) (q := q)).symm w
  refine ⟨fun p => (G : AddCircle P × Space → CVec3) ((p.1 : AddCircle P), p.2), ?_, ?_⟩
  · refine (Lp.stronglyMeasurable G).comp_measurable ?_
    exact (AddCircle.measurable_mk'.comp measurable_fst).prodMk measurable_snd
  · exact ae_comp_mk (FreeStress.prodLpEquiv_symm_ae w)

theorem IsRep.slice_shift {w : Yq P q} {W : ℝ × Space → CVec3} (hW : IsRep w W) (τ₀ : ℝ) :
    ∀ᵐ t : ℝ, (fun y => W (τ₀ + t, y)) =ᵐ[volume]
      (w ((τ₀ + t : ℝ) : AddCircle P) : Space → CVec3) :=
  (measurePreserving_add_left (volume : Measure ℝ) τ₀).quasiMeasurePreserving.ae hW.slice

/-! ### Window integrals of `‖w(τ)‖_q^q` -/

theorem lintegral_window_lt_top (hq : q ≠ ⊤) (w : Yq P q) (τ₀ a b : ℝ) :
    ∫⁻ t in Icc a b, ‖w ((τ₀ + t : ℝ) : AddCircle P)‖ₑ ^ q.toReal < ⊤ := by
  have hP0 := hP.out
  set n : ℕ := ⌈(b - a + 1) / P⌉₊
  have hn : b - a + 1 ≤ n * P := by
    have : (b - a + 1) / P ≤ n := Nat.le_ceil _
    rwa [div_le_iff₀ hP0] at this
  have hsub : Icc a b ⊆ Ioc (a - 1) (a - 1 + n * P) := fun t ht => ⟨by linarith [ht.1],
    by linarith [ht.2]⟩
  refine (lintegral_mono_set hsub).trans_lt ?_
  rw [lintegral_Ioc_nat_period (fun τ => ‖w τ‖ₑ ^ q.toReal) τ₀ (a - 1) n,
    AddCircle.volume_eq_smul_haarAddCircle, lintegral_smul_measure,
    lintegral_enorm_rpow_Yq w hq]
  refine ENNReal.mul_lt_top (ENNReal.natCast_lt_top n) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
  exact ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg (by rw [Lp.enorm_def]; exact Lp.eLpNorm_ne_top w)

/-! ### The pullback `v` -/

/-- `v(t, x) = e^{-t/2} W(τ₀ + t, e^{-t/2} x)` (tex 7485–7486). -/
def vfun (τ₀ : ℝ) (W : ℝ × Space → CVec3) (p : ℝ × Space) : CVec3 :=
  Real.exp (-(p.1 / 2)) • W (τ₀ + p.1, Real.exp (-(p.1 / 2)) • p.2)

theorem stronglyMeasurable_vfun {W : ℝ × Space → CVec3} (hW : StronglyMeasurable W) (τ₀ : ℝ) :
    StronglyMeasurable (vfun τ₀ W) := by
  unfold vfun
  refine (Real.continuous_exp.comp (continuous_fst.div_const 2).neg).stronglyMeasurable.smul
    (hW.comp_measurable ?_)
  fun_prop

theorem vfun_dilChart (τ₀ : ℝ) (W : ℝ × Space → CVec3) (p : ℝ × Space) :
    vfun τ₀ W (dilChart p) = Real.exp (-(p.1 / 2)) • W (τ₀ + p.1, p.2) := by
  simp only [vfun, dilChart, smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul]

/-- `∫ m(t) |W(τ₀ + t, y)|^q dt dy = ∫ m(t) ‖w(τ₀ + t)‖_q^q dt`. -/
theorem lintegral_rep (hq : q ≠ ⊤) {w : Yq P q} {W : ℝ × Space → CVec3} (hW : IsRep w W)
    (τ₀ : ℝ) {m : ℝ → ℝ≥0∞} (hm : Measurable m) :
    ∫⁻ p : ℝ × Space, m p.1 * ‖W (τ₀ + p.1, p.2)‖ₑ ^ q.toReal =
      ∫⁻ t, m t * ‖w ((τ₀ + t : ℝ) : AddCircle P)‖ₑ ^ q.toReal := by
  have hWm : Measurable fun p : ℝ × Space => ‖W (τ₀ + p.1, p.2)‖ₑ ^ q.toReal := by
    have h1 : Measurable fun p : ℝ × Space => W (τ₀ + p.1, p.2) :=
      hW.meas.measurable.comp (by fun_prop)
    exact h1.enorm.pow_const _
  rw [Measure.volume_eq_prod]
  have hmeas : AEMeasurable (fun p : ℝ × Space => m p.1 * ‖W (τ₀ + p.1, p.2)‖ₑ ^ q.toReal)
      (volume.prod volume) := ((hm.comp measurable_fst).mul hWm).aemeasurable
  rw [lintegral_prod _ hmeas]
  refine lintegral_congr_ae ?_
  filter_upwards [hW.slice_shift τ₀] with t ht
  have hmt : Measurable fun y : Space => ‖W (τ₀ + t, y)‖ₑ ^ q.toReal :=
    (hW.meas.measurable.comp (by fun_prop : Measurable fun y : Space => (τ₀ + t, y))).enorm.pow_const _
  rw [lintegral_const_mul (m t) hmt]
  congr 1
  rw [← lintegral_enorm_rpow_Lp _ hq]
  refine lintegral_congr_ae ?_
  filter_upwards [ht] with y hy
  rw [hy]

end UnforcedLeray.Short.PartIIa.Rep
