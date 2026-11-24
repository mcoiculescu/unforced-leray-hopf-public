import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Defs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.WeakMulRule.Conv
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.WeakMulRule.Smooth
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.WeakMulRule.Holder

/-!
# `WeakMulRule`: decomposition into the a.e.-in-`τ` bridging lemmas

Source `the November 2 reference manuscript`
lines 2562-2564 (local Friedrichs argument in `y`), phase tests 2525-2531.

Spatial mollifications `a_n = spatMol ρ_n f` are smooth in `y` only for a.e. `τ` (the slice of a
`MemLpLoc` function is locally integrable only for a.e. `τ`), and `dyS a_n = spatMol ρ_n Df`
only for a.e. `τ`.  The four `Prop`s below are the true source facts; `weakMulRule_of` assembles
the weak product rule from them, the compiled helpers `spatMol_tendsto_lp`, `phaseInt_tendsto_of_holder`
and the a.e. product rule `weakDyS_mul_smooth_ae` proved here.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal
open UnforcedLeray.Cons.C03.Concrete (phaseInt)

/-- Existence of a spatial approximate identity (`ContDiffBump`, normalised). -/
def ExistsApproxId : Prop := ∃ ρ : ℕ → UnforcedLeray.Space → ℝ, IsApproxId ρ

/-- Mollification preserves `MemLpLoc` (Minkowski/Young for `ρ ≥ 0`, `∫ρ = 1`, compact support,
localised on `(0,P] × B(0,R)` using `SpatMolContract` on `B(0,R+r)`; source 2562-2564). -/
def SpatMolMemLoc : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (ρ : UnforcedLeray.Space → ℝ), ContDiff ℝ ∞ ρ → HasCompactSupport ρ →
    (∀ y, 0 ≤ ρ y) → ∫ y, ρ y = 1 → ∀ (f : ℝ × UnforcedLeray.Space → ℂ) (p : ℝ≥0∞), 1 ≤ p → p ≠ ⊤ →
      MemLpLoc P f p → MemLpLoc P (spatMol ρ f) p

/-- For `f ∈ L^1_loc` of the cell, for a.e. `τ ∈ (0,P]` the `y`-slice of `f` is locally
integrable (Fubini), hence `y ↦ spatMol ρ f (τ,y)` is `C^∞` (convolution of a locally integrable
function with a smooth compactly supported kernel). -/
def SpatMolSliceSmooth : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (ρ : UnforcedLeray.Space → ℝ), ContDiff ℝ ∞ ρ → HasCompactSupport ρ →
    ∀ f : ℝ × UnforcedLeray.Space → ℂ, MemLpLoc P f 1 →
      ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) P)), ContDiff ℝ 1 (fun y => spatMol ρ f (τ, y))

/-- If `∂_{y_j} f = Df` weakly on the cell (`f, Df ∈ L^1_loc`), then for a.e. `τ` the classical
slice derivative of `spatMol ρ f` is `spatMol ρ Df`: test the weak identity against
`θ(τ) ψ(y)` with `ψ` ranging over a countable family dense in `C_c^∞` (or use
`ae_eq_zero_of_integral_contDiff_smul_eq_zero`) to get the slice identity for a.e. `τ`, then
differentiate the convolution under the integral. -/
def DySSpatMolAe : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (j : Fin 3) (ρ : UnforcedLeray.Space → ℝ), ContDiff ℝ ∞ ρ →
    HasCompactSupport ρ → ∀ f Df : ℝ × UnforcedLeray.Space → ℂ, MemLpLoc P f 1 → MemLpLoc P Df 1 →
      WeakDyS P j f Df →
      ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) P)), ∀ y,
        dyS j (spatMol ρ f) (τ, y) = spatMol ρ Df (τ, y)

/-- **Lemma C, a.e. form.**  Product rule for functions that are `C¹` in `y` for a.e. `τ`. -/
theorem weakDyS_mul_smooth_ae (P : ℝ) [Fact (0 < P)] (j : Fin 3)
    (a b : ℝ × UnforcedLeray.Space → ℂ)
    (ha : ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) P)), ContDiff ℝ 1 (fun y => a (τ, y)))
    (hb : ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) P)), ContDiff ℝ 1 (fun y => b (τ, y))) :
    WeakDyS P j (fun x => a x * b x) (fun x => dyS j a x * b x + a x * dyS j b x) := by
  intro φ hφ
  obtain ⟨R, hR⟩ := hφ.bounded_support
  unfold phaseInt
  rw [← smul_neg]
  congr 1
  rw [← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [ha, hb] with τ ha hb
  set ψ : UnforcedLeray.Space → ℂ := fun y => φ (τ, y) with hψ
  set F : UnforcedLeray.Space → ℂ := fun y => a (τ, y) * b (τ, y) with hF
  have hψs : ContDiff ℝ ∞ ψ := hφ.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hψc : HasCompactSupport ψ :=
    HasCompactSupport.intro (isCompact_closedBall (0 : UnforcedLeray.Space) R) fun y hy => by
      apply hR
      simpa [not_le] using hy
  have hFs : ContDiff ℝ 1 F := ha.mul hb
  have hψ1 : Continuous (fun y => fderiv ℝ ψ y (coordinateVector j)) :=
    ((hψs.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hF1 : Continuous (fun y => fderiv ℝ F y (coordinateVector j)) :=
    ((hFs.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hψ1c : HasCompactSupport (fun y => fderiv ℝ ψ y (coordinateVector j)) :=
    hψc.fderiv_apply (𝕜 := ℝ) (coordinateVector j)
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure UnforcedLeray.Space)) (f := ψ) (g := F)
    (v := coordinateVector j)
    ((hψ1.mul hFs.continuous).integrable_of_hasCompactSupport hψ1c.mul_right)
    ((hψs.continuous.mul hF1).integrable_of_hasCompactSupport hψc.mul_right)
    ((hψs.continuous.mul hFs.continuous).integrable_of_hasCompactSupport hψc.mul_right)
    (fun x _ => (hψs.differentiable (by simp)) x)
    (fun x _ => (hFs.differentiable (by simp)) x)
  have hdy : ∀ y, dy j φ (τ, y) = fderiv ℝ ψ y (coordinateVector j) := by
    intro y
    have := congrFun (dy_eq_dyS j (hφ.smooth.differentiable (by simp))) (τ, y)
    simpa [dyS] using this
  have hprod : ∀ y, fderiv ℝ F y (coordinateVector j) =
      dyS j a (τ, y) * b (τ, y) + a (τ, y) * dyS j b (τ, y) := by
    intro y
    have h1 := (ha.differentiable (by simp)) y
    have h2 := (hb.differentiable (by simp)) y
    rw [hF, fderiv_fun_mul h1 h2]
    simp [dyS]
    ring
  simp only [hdy, hprod] at key ⊢
  rw [key, neg_neg]

/-- The cell measure `(0,P] × B(0,R)`. -/
def cellMeas (P R : ℝ) : Measure (ℝ × UnforcedLeray.Space) :=
  (volume.restrict (Ioc (0 : ℝ) P)).prod (volume.restrict (Metric.closedBall 0 R))

instance cellMeas_finite (P R : ℝ) : IsFiniteMeasure (cellMeas P R) := by
  unfold cellMeas
  have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) P)) := ⟨by simp⟩
  have : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : UnforcedLeray.Space) R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_closedBall_lt_top⟩
  infer_instance

theorem cellMeas_eq (P R : ℝ) : cellMeas P R = (volume : Measure (ℝ × UnforcedLeray.Space)).restrict
    (Ioc (0 : ℝ) P ×ˢ Metric.closedBall 0 R) := by
  rw [cellMeas, Measure.prod_restrict, Measure.volume_eq_prod]

theorem integrable_phase_mul (P R : ℝ) [Fact (0 < P)] (φ : ℝ × UnforcedLeray.Space → ℂ)
    (hφ : IsPhaseTest P φ) (f : ℝ × UnforcedLeray.Space → ℂ)
    (hf : Integrable f (cellMeas P R)) : Integrable (fun x => φ x * f x) (cellMeas P R) := by
  have hφc : Continuous φ := hφ.smooth.continuous
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := P)).prod
    (isCompact_closedBall (0 : UnforcedLeray.Space) R) |>.exists_bound_of_continuousOn
    hφc.continuousOn
  have hCae : ∀ᵐ x ∂(cellMeas P R), ‖φ x‖ ≤ C := by
    rw [cellMeas_eq]
    refine (ae_restrict_mem (measurableSet_Ioc.prod measurableSet_closedBall)).mono fun x hx => ?_
    exact hC x ⟨Ioc_subset_Icc_self hx.1, hx.2⟩
  exact hf.bdd_mul hφc.aestronglyMeasurable hCae

theorem phaseInt_reduce (P R : ℝ) [Fact (0 < P)] (φ : ℝ × UnforcedLeray.Space → ℂ)
    (hsupp : ∀ τ y, R < ‖y‖ → φ (τ, y) = 0) (f : ℝ × UnforcedLeray.Space → ℂ)
    (hf : Integrable (fun x => φ x * f x) (cellMeas P R)) :
    phaseInt P (fun x => φ x * f x) = P⁻¹ • ∫ x, φ x * f x ∂(cellMeas P R) := by
  unfold phaseInt
  congr 1
  rw [cellMeas, integral_prod _ hf]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only
  symm
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
  rw [hsupp t y (by simpa [not_le] using hy), zero_mul]

theorem phaseInt_add_mul (P R : ℝ) [Fact (0 < P)] (φ : ℝ × UnforcedLeray.Space → ℂ)
    (hφ : IsPhaseTest P φ) (hsupp : ∀ τ y, R < ‖y‖ → φ (τ, y) = 0)
    (f₁ f₂ : ℝ × UnforcedLeray.Space → ℂ)
    (h₁ : Integrable f₁ (cellMeas P R)) (h₂ : Integrable f₂ (cellMeas P R)) :
    phaseInt P (fun x => φ x * (f₁ x + f₂ x)) =
      phaseInt P (fun x => φ x * f₁ x) + phaseInt P (fun x => φ x * f₂ x) := by
  have i₁ := integrable_phase_mul P R φ hφ f₁ h₁
  have i₂ := integrable_phase_mul P R φ hφ f₂ h₂
  have i₃ : Integrable (fun x => φ x * (f₁ x + f₂ x)) (cellMeas P R) := by
    simp only [mul_add]; exact i₁.add i₂
  rw [phaseInt_reduce P R φ hsupp _ i₁, phaseInt_reduce P R φ hsupp _ i₂,
    phaseInt_reduce P R φ hsupp _ i₃, ← smul_add, ← integral_add i₁ i₂]
  simp only [mul_add]

theorem phaseInt_congr_ae (P : ℝ) (F G : ℝ × UnforcedLeray.Space → ℂ)
    (h : ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) P)), ∀ y, F (τ, y) = G (τ, y)) :
    phaseInt P F = phaseInt P G := by
  unfold phaseInt
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [h] with τ hτ
  exact integral_congr_ae (Eventually.of_forall fun y => hτ y)

theorem phaseInt_tendsto_unique {α : Type*} {l : Filter α} [l.NeBot] {u : α → ℂ} {a b : ℂ}
    (ha : Tendsto u l (𝓝 a)) (hb : Tendsto u l (𝓝 b)) : a = b := tendsto_nhds_unique ha hb

theorem q0E_facts :
    (1 ≤ UnforcedLeray.B0412.q0E ∧ UnforcedLeray.B0412.q0E ≠ ⊤) ∧
    (1 ≤ 2 * UnforcedLeray.B0412.q0E ∧ 2 * UnforcedLeray.B0412.q0E ≠ ⊤) ∧
    (1 / (2 * UnforcedLeray.B0412.q0E) + 1 / (2 * UnforcedLeray.B0412.q0E) ≤ 1) ∧
    (1 / UnforcedLeray.B0412.q0E + 1 / (2 * UnforcedLeray.B0412.q0E) ≤ 1) ∧
    (1 / (2 * UnforcedLeray.B0412.q0E) + 1 / UnforcedLeray.B0412.q0E ≤ 1) := by
  have hq : UnforcedLeray.B0412.q0E = ENNReal.ofReal (11 / 4) := rfl
  have hq2 : 2 * UnforcedLeray.B0412.q0E = ENNReal.ofReal (11 / 2) := by
    rw [hq, show (11 / 2 : ℝ) = 2 * (11 / 4) by norm_num, ENNReal.ofReal_mul (by norm_num)]
    simp
  have hi1 : 1 / UnforcedLeray.B0412.q0E = ENNReal.ofReal (4 / 11) := by
    rw [hq, one_div, ← ENNReal.ofReal_inv_of_pos (by norm_num)]; norm_num
  have hi2 : 1 / (2 * UnforcedLeray.B0412.q0E) = ENNReal.ofReal (2 / 11) := by
    rw [hq2, one_div, ← ENNReal.ofReal_inv_of_pos (by norm_num)]; norm_num
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hq]; exact ENNReal.one_le_ofReal.mpr (by norm_num)
  · rw [hq]; exact ENNReal.ofReal_ne_top
  · rw [hq2]; exact ENNReal.one_le_ofReal.mpr (by norm_num)
  · rw [hq2]; exact ENNReal.ofReal_ne_top
  · rw [hi2, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    exact ENNReal.ofReal_le_one.mpr (by norm_num)
  · rw [hi1, hi2, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    exact ENNReal.ofReal_le_one.mpr (by norm_num)
  · rw [hi1, hi2, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    exact ENNReal.ofReal_le_one.mpr (by norm_num)

theorem weakMulRule_of (hApprox : ExistsApproxId) (hMem : SpatMolMemLoc)
    (hSm : SpatMolSliceSmooth) (hDy : DySSpatMolAe) : WeakMulRule := by
  intro P _ j f g Df Dg hf hg hDf hDg hWf hWg
  obtain ⟨ρ, hρ⟩ := hApprox
  obtain ⟨⟨hq1, hqt⟩, ⟨h2q1, h2qt⟩, e1, e2, e3⟩ := q0E_facts
  set q := UnforcedLeray.B0412.q0E with hqdef
  have l1 : ∀ h : ℝ × UnforcedLeray.Space → ℂ, MemLpLoc P h q → MemLpLoc P h 1 := by
    intro h hh R
    haveI := cellMeas_finite P R
    exact (hh R).mono_exponent (μ := cellMeas P R) hq1
  have l1' : ∀ h : ℝ × UnforcedLeray.Space → ℂ, MemLpLoc P h (2 * q) → MemLpLoc P h 1 := by
    intro h hh R
    haveI := cellMeas_finite P R
    exact (hh R).mono_exponent (μ := cellMeas P R) h2q1
  have mol : ∀ (h : ℝ × UnforcedLeray.Space → ℂ) (p : ℝ≥0∞), 1 ≤ p → p ≠ ⊤ → MemLpLoc P h p →
      ∀ n, MemLpLoc P (spatMol (ρ n) h) p := fun h p hp hpt hh n =>
    hMem P (ρ n) (hρ n).1 (hρ n).2.1 (hρ n).2.2.1 (hρ n).2.2.2.1 h p hp hpt hh
  have hconv : ∀ (h : ℝ × UnforcedLeray.Space → ℂ) (p : ℝ≥0∞), 1 ≤ p → p ≠ ⊤ → MemLpLoc P h p →
      ∀ R : ℝ, Tendsto (fun n => eLpNorm (spatMol (ρ n) h - h) p (cellMeas P R)) atTop (𝓝 0) :=
    fun h p hp hpt hh R => spatMol_tendsto_lp P R p hp hpt h hh ρ hρ
  intro φ hφ
  obtain ⟨R₁, hR₁⟩ := hφ.bounded_support
  obtain ⟨R₂, hR₂⟩ := (hφ.dy j).bounded_support
  set R := max R₁ R₂ with hR
  have s1 : ∀ τ y, R < ‖y‖ → φ (τ, y) = 0 := fun τ y hy =>
    hR₁ τ y (lt_of_le_of_lt (le_max_left _ _) hy)
  have s2 : ∀ τ y, R < ‖y‖ → dy j φ (τ, y) = 0 := fun τ y hy =>
    hR₂ τ y (lt_of_le_of_lt (le_max_right _ _) hy)
  have hmem : ∀ (h : ℝ × UnforcedLeray.Space → ℂ) (p : ℝ≥0∞), MemLpLoc P h p →
      MemLp h p (cellMeas P R) := fun h p hh => hh R
  -- the exact identity at level `n`
  have hn : ∀ n, phaseInt P (fun x => dy j φ x * (spatMol (ρ n) f x * spatMol (ρ n) g x)) =
      -(phaseInt P (fun x => φ x * (spatMol (ρ n) Df x * spatMol (ρ n) g x)) +
        phaseInt P (fun x => φ x * (spatMol (ρ n) f x * spatMol (ρ n) Dg x))) := by
    intro n
    have hw := weakDyS_mul_smooth_ae P j (spatMol (ρ n) f) (spatMol (ρ n) g)
      (hSm P (ρ n) (hρ n).1 (hρ n).2.1 f (l1' f hf))
      (hSm P (ρ n) (hρ n).1 (hρ n).2.1 g (l1' g hg)) φ hφ
    have hwf := hDy P j (ρ n) (hρ n).1 (hρ n).2.1 f Df (l1' f hf) (l1 Df hDf) hWf
    have hwg := hDy P j (ρ n) (hρ n).1 (hρ n).2.1 g Dg (l1' g hg) (l1 Dg hDg) hWg
    simp only at hw
    rw [hw]
    congr 1
    rw [← phaseInt_add_mul P R φ hφ s1]
    · refine phaseInt_congr_ae P _ _ ?_
      filter_upwards [hwf, hwg] with τ h1 h2 y
      rw [h1 y, h2 y]
    · exact integrable_mul_holder (μ := cellMeas P R) e2 (hmem _ _ (mol Df q hq1 hqt hDf n))
        (hmem _ _ (mol g (2 * q) h2q1 h2qt hg n))
    · exact integrable_mul_holder (μ := cellMeas P R) e3 (hmem _ _ (mol f (2 * q) h2q1 h2qt hf n))
        (hmem _ _ (mol Dg q hq1 hqt hDg n))
  have L1 := phaseInt_tendsto_of_holder P R (dy j φ) (hφ.dy j) s2
    (fun n => spatMol (ρ n) f) (fun n => spatMol (ρ n) g) f g (2 * q) (2 * q) e1
    (mol f _ h2q1 h2qt hf) (mol g _ h2q1 h2qt hg) hf hg
    (hconv f _ h2q1 h2qt hf R) (hconv g _ h2q1 h2qt hg R)
  have L2 := phaseInt_tendsto_of_holder P R φ hφ s1
    (fun n => spatMol (ρ n) Df) (fun n => spatMol (ρ n) g) Df g q (2 * q) e2
    (mol Df _ hq1 hqt hDf) (mol g _ h2q1 h2qt hg) hDf hg
    (hconv Df _ hq1 hqt hDf R) (hconv g _ h2q1 h2qt hg R)
  have L3 := phaseInt_tendsto_of_holder P R φ hφ s1
    (fun n => spatMol (ρ n) f) (fun n => spatMol (ρ n) Dg) f Dg (2 * q) q e3
    (mol f _ h2q1 h2qt hf) (mol Dg _ hq1 hqt hDg) hf hDg
    (hconv f _ h2q1 h2qt hf R) (hconv Dg _ hq1 hqt hDg R)
  have L4 := (L2.add L3).neg
  have L5 : Tendsto (fun n => phaseInt P (fun x => dy j φ x * (spatMol (ρ n) f x * spatMol (ρ n) g x)))
      atTop (𝓝 (-(phaseInt P (fun x => φ x * (Df x * g x)) +
        phaseInt P (fun x => φ x * (f x * Dg x))))) := by
    simpa only [hn] using L4
  have key := tendsto_nhds_unique L1 L5
  show phaseInt P (fun x => dy j φ x * (f x * g x)) = _
  rw [key, phaseInt_add_mul P R φ hφ s1 _ _
    (integrable_mul_holder (μ := cellMeas P R) e2 (hmem _ _ hDf) (hmem _ _ hg))
    (integrable_mul_holder (μ := cellMeas P R) e3 (hmem _ _ hf) (hmem _ _ hDg))]

end UnforcedLeray.Short.PartIIIb.Concrete
