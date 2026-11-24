import UnforcedLeray.Units.B0656.Spaces
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# B0656, part 3: the weighted periodic Sobolev spaces `H^k_m` and `H^{-k}_m`

Blueprint unit **B0656** (`unlabeled:13869`), `paper/main.tex` lines 13879–13888.

Derivatives are periodic weak derivatives (`paper/main.tex`, lines 13851–13852: "Derivatives
are periodic weak derivatives, never derivatives of zero extensions"). The test functions are
the smooth functions on the plane that are `ℓ`-periodic in `q` and vanish for large `|η|`, that
is, the smooth compactly supported functions on the cylinder. They need not vanish at the seams
of the cell. For a multi-index `α = (α_q, α_η)`, `g` is the weak derivative `D^α f` when
`∫ f D^α φ = (-1)^{|α|} ∫ g φ` over one cell for every test `φ`. Both integrands are
integrable for `f, g ∈ X_m` (`integrable_mul_test`), so no Bochner junk value enters.

`H^k_m = {f : D^α f ∈ X_m, |α| ≤ k}` is realized, following
`UnforcedLeray/Analysis/SobolevGraph/H1.lean`, as the closed subspace of the Hilbert sum
`⊕_{|α| ≤ k} X_m` cut out by the weak-derivative identities; its norm is
`(∑_{|α|≤k} ‖D^α f‖²_{X_m})^{1/2}`. Weak derivatives are unique (`HasWeakDeriv.unique`, through
the fundamental lemma of the calculus of variations and a periodization of compactly supported
tests), so the value map `H^k_m → X_m` is injective and its range is exactly
`{f ∈ X_m : D^α f ∈ X_m for |α| ≤ k}` (`mem_range_value_iff`). Finally
`H^{-k}_m = (H^k_{-m})^*` is the strong dual.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.B0656

theorem weightMeasure_def (ℓ m : ℝ) :
    weightMeasure ℓ m = (cellMeasure ℓ).withDensity (weightDensity ℓ m) := rfl

/-- Almost-everywhere statements for `ρ_ℓ^m dq dη` hold for `dq dη`, and conversely. -/
theorem ae_cell_of_ae_weight {ℓ m : ℝ} {p : Plane → Prop}
    (h : ∀ᵐ z ∂(weightMeasure ℓ m), p z) : ∀ᵐ z ∂(cellMeasure ℓ), p z := by
  rwa [← ae_weightMeasure ℓ m]

theorem ae_weight_of_ae_cell {ℓ m : ℝ} {p : Plane → Prop}
    (h : ∀ᵐ z ∂(cellMeasure ℓ), p z) : ∀ᵐ z ∂(weightMeasure ℓ m), p z := by
  rwa [ae_weightMeasure ℓ m]

/-! ### Bounded functions with compact support on the cell lie in every `X_m` -/

theorem memLp_weight_of_le_indicator (ℓ m : ℝ) {ψ : Plane → ℝ}
    (hψ : AEStronglyMeasurable ψ (cellMeasure ℓ)) {K : Set Plane} (hK : IsCompact K) (M : ℝ)
    (hbound : ∀ z ∈ cell ℓ, |ψ z| ≤ K.indicator (fun _ => M) z) :
    MemLp ψ 2 (weightMeasure ℓ m) := by
  have hS := isSqrtDensity_weight ℓ m
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (continuous_rho_rpow ℓ (m / 2)).continuousOn
  have hmem : MemLp (K.indicator fun _ => B * M) 2 (cellMeasure ℓ) :=
    memLp_indicator_const 2 hK.measurableSet _
      (Or.inr (ne_of_lt (lt_of_le_of_lt (Measure.restrict_apply_le _ _) hK.measure_lt_top)))
  have hprod : MemLp (fun z => sqrtWeight ℓ m z * ψ z) 2 (cellMeasure ℓ) := by
    refine hmem.of_le (hS.measurable.aestronglyMeasurable.mul hψ) ?_
    refine (ae_restrict_iff' (measurableSet_cell ℓ)).2 (ae_of_all _ fun z hz => ?_)
    have hb := hbound z hz
    by_cases hzK : z ∈ K
    · rw [indicator_of_mem hzK] at hb ⊢
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      have h1 : |sqrtWeight ℓ m z| ≤ B := by
        have := hB z hzK
        rwa [Real.norm_eq_abs] at this
      calc |sqrtWeight ℓ m z| * |ψ z| ≤ B * M :=
            mul_le_mul h1 hb (abs_nonneg _) ((abs_nonneg _).trans h1)
        _ ≤ |B * M| := le_abs_self _
    · rw [indicator_of_notMem hzK] at hb ⊢
      have : ψ z = 0 := abs_nonpos_iff.1 hb
      simp [this]
  refine ⟨hψ.mono_ac (IsSqrtDensity.absCont' _), ?_⟩
  rw [weightMeasure_def, hS.eLpNorm_eq]
  exact hprod.eLpNorm_lt_top

/-- Continuous functions vanishing for `|η| > R`. -/
def IsContBdd (ψ : Plane → ℝ) : Prop :=
  Continuous ψ ∧ ∃ R : ℝ, ∀ z : Plane, R < |z.2| → ψ z = 0

theorem IsContBdd.memLp (ℓ m : ℝ) {ψ : Plane → ℝ} (h : IsContBdd ψ) :
    MemLp ψ 2 (weightMeasure ℓ m) := by
  obtain ⟨hc, R, hR⟩ := h
  set K : Set Plane := Icc (-(ℓ / 2)) (ℓ / 2) ×ˢ Icc (-R) R
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  apply memLp_weight_of_le_indicator ℓ m hc.aestronglyMeasurable hK M
  intro z hz
  by_cases hzK : z ∈ K
  · rw [indicator_of_mem hzK]
    have := hM z hzK
    rwa [Real.norm_eq_abs] at this
  · rw [indicator_of_notMem hzK]
    have hlt : R < |z.2| := lt_of_not_ge fun hle =>
      hzK ⟨Ioo_subset_Icc_self (mem_prod.1 hz).1, abs_le.1 hle⟩
    simp [hR z hlt]

/-- The class in `X_m` of a continuous function vanishing for large `|η|`. -/
def ofContBdd (ℓ m : ℝ) (ψ : Plane → ℝ) (h : IsContBdd ψ) : X ℓ m :=
  (h.memLp ℓ m).toLp ψ

theorem coeFn_ofContBdd (ℓ m : ℝ) (ψ : Plane → ℝ) (h : IsContBdd ψ) :
    (ofContBdd ℓ m ψ h : Plane → ℝ) =ᵐ[cellMeasure ℓ] ψ :=
  ae_cell_of_ae_weight (h.memLp ℓ m).coeFn_toLp

/-- Pairing an element of `X_m` with such a function is the duality `dualX`. -/
theorem dualX_ofContBdd (ℓ m : ℝ) (f : X ℓ m) (ψ : Plane → ℝ) (h : IsContBdd ψ) :
    dualX ℓ m (ofContBdd ℓ (-m) ψ h) f = ∫ z, f z * ψ z ∂(cellMeasure ℓ) := by
  rw [dualX_apply]
  apply integral_congr_ae
  filter_upwards [coeFn_ofContBdd ℓ (-m) ψ h] with z hz
  rw [hz]

theorem integrable_mul_contBdd (ℓ m : ℝ) (f : X ℓ m) (ψ : Plane → ℝ) (h : IsContBdd ψ) :
    Integrable (fun z => f z * ψ z) (cellMeasure ℓ) := by
  refine (integrable_mul_X ℓ m f (ofContBdd ℓ (-m) ψ h)).congr ?_
  filter_upwards [coeFn_ofContBdd ℓ (-m) ψ h] with z hz
  rw [hz]

/-! ### Periodic test functions and periodic weak derivatives -/

/-- A test function on the cylinder of period `ℓ`: smooth on the plane, `ℓ`-periodic in `q`,
and zero for large `|η|`. It need not vanish at the seams `q = ±ℓ/2`. -/
structure IsPeriodicTest (ℓ : ℝ) (φ : Plane → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ φ
  periodic : ∀ q η : ℝ, φ (q + ℓ, η) = φ (q, η)
  bounded : ∃ R : ℝ, ∀ z : Plane, R < |z.2| → φ z = 0

theorem tsupport_subset_of_bounded {φ : Plane → ℝ} {R : ℝ}
    (h : ∀ z : Plane, R < |z.2| → φ z = 0) : tsupport φ ⊆ {z : Plane | |z.2| ≤ R} :=
  closure_minimal (fun z hz => le_of_not_gt fun hlt => hz (h z hlt))
    (isClosed_le (continuous_abs.comp continuous_snd) continuous_const)

theorem IsPeriodicTest.partialMulti_isContBdd {ℓ : ℝ} {φ : Plane → ℝ}
    (hφ : IsPeriodicTest ℓ φ) (α : ℕ × ℕ) : IsContBdd (partialMulti α φ) := by
  obtain ⟨R, hR⟩ := hφ.bounded
  refine ⟨?_, R, fun z hz => ?_⟩
  · exact (hφ.smooth.continuous_iteratedFDeriv (by exact_mod_cast le_top)).eval_const _
  · have hz' : z ∉ tsupport φ := fun hmem =>
      absurd (tsupport_subset_of_bounded hR hmem) (not_le.2 hz)
    have : iteratedFDeriv ℝ (α.1 + α.2) φ z = 0 :=
      Function.notMem_support.1 fun hs => hz' (support_iteratedFDeriv_subset _ hs)
    simp [partialMulti, this]

theorem partialMulti_zero (φ : Plane → ℝ) : partialMulti (0, 0) φ = φ := by
  funext z
  simp [partialMulti]

theorem IsPeriodicTest.isContBdd {ℓ : ℝ} {φ : Plane → ℝ} (hφ : IsPeriodicTest ℓ φ) :
    IsContBdd φ := by
  have := hφ.partialMulti_isContBdd (0, 0)
  rwa [partialMulti_zero] at this

/-- For `f ∈ X_m` and a periodic test `φ`, the integrands `f D^α φ` of the weak-derivative
identity are integrable. -/
theorem integrable_mul_test (ℓ m : ℝ) (f : X ℓ m) {φ : Plane → ℝ} (hφ : IsPeriodicTest ℓ φ)
    (α : ℕ × ℕ) : Integrable (fun z => f z * partialMulti α φ z) (cellMeasure ℓ) :=
  integrable_mul_contBdd ℓ m f _ (hφ.partialMulti_isContBdd α)

/-- `g = D^α f` in the periodic weak sense, for `f, g ∈ X_m`: for every periodic test `φ`,
`∫ f D^α φ dq dη = (-1)^{|α|} ∫ g φ dq dη` over one cell (`paper/main.tex`, line 13882,
with the derivative convention of lines 13851–13852). -/
def HasWeakDeriv (ℓ m : ℝ) (α : ℕ × ℕ) (f g : X ℓ m) : Prop :=
  ∀ φ : Plane → ℝ, IsPeriodicTest ℓ φ →
    ∫ z, f z * partialMulti α φ z ∂(cellMeasure ℓ) =
      (-1) ^ (α.1 + α.2) * ∫ z, g z * φ z ∂(cellMeasure ℓ)

theorem hasWeakDeriv_zero (ℓ m : ℝ) (f : X ℓ m) : HasWeakDeriv ℓ m (0, 0) f f := by
  intro φ _
  simp [partialMulti_zero]

/-! ### Uniqueness of periodic weak derivatives -/

/-- The `ℓ`-periodization of a function supported in the open cell: its values on the cell,
continued periodically in `q`. -/
def periodize {ℓ : ℝ} (hℓ : 0 < ℓ) (g : Plane → ℝ) (z : Plane) : ℝ :=
  g (toIcoMod hℓ (-(ℓ / 2)) z.1, z.2)

theorem periodize_eq_local {ℓ : ℝ} (hℓ : 0 < ℓ) {g : Plane → ℝ}
    (hg : ∀ w : Plane, g w ≠ 0 → w.1 ∈ Ioo (-(ℓ / 2)) (ℓ / 2)) (n : ℤ) (z : Plane)
    (hz : z.1 - n • ℓ ∈ Ioo (-(3 * ℓ / 2)) (3 * ℓ / 2)) :
    periodize hℓ g z =
      g (z.1 - n • ℓ - ℓ, z.2) + g (z.1 - n • ℓ, z.2) + g (z.1 - n • ℓ + ℓ, z.2) := by
  have hvan : ∀ y : ℝ, y ∉ Ioo (-(ℓ / 2)) (ℓ / 2) → g (y, z.2) = 0 := fun y hy => by
    by_contra hne
    exact hy (hg (y, z.2) hne)
  set x := z.1 - n • ℓ with hx
  obtain ⟨hx1, hx2⟩ := hz
  unfold periodize
  rcases lt_or_ge x (-(ℓ / 2)) with h1 | h1
  · have hmod : toIcoMod hℓ (-(ℓ / 2)) z.1 = x + ℓ := by
      rw [toIcoMod_eq_iff]
      refine ⟨⟨by linarith, by linarith⟩, n - 1, ?_⟩
      rw [hx, sub_smul, one_smul]
      ring
    rw [hmod, hvan (x - ℓ) (fun h => by linarith [h.1]), hvan x (fun h => by linarith [h.1])]
    ring
  rcases lt_or_ge x (ℓ / 2) with h2 | h2
  · have hmod : toIcoMod hℓ (-(ℓ / 2)) z.1 = x := by
      rw [toIcoMod_eq_iff]
      refine ⟨⟨h1, by linarith⟩, n, ?_⟩
      rw [hx]
      ring
    rw [hmod, hvan (x - ℓ) (fun h => by linarith [h.1]), hvan (x + ℓ) (fun h => by linarith [h.2])]
    ring
  · have hmod : toIcoMod hℓ (-(ℓ / 2)) z.1 = x - ℓ := by
      rw [toIcoMod_eq_iff]
      refine ⟨⟨by linarith, by linarith⟩, n + 1, ?_⟩
      rw [hx, add_smul, one_smul]
      ring
    rw [hmod, hvan x (fun h => by linarith [h.2]), hvan (x + ℓ) (fun h => by linarith [h.2])]
    ring

theorem contDiff_periodize {ℓ : ℝ} (hℓ : 0 < ℓ) {g : Plane → ℝ} (hgs : ContDiff ℝ ∞ g)
    (hg : ∀ w : Plane, g w ≠ 0 → w.1 ∈ Ioo (-(ℓ / 2)) (ℓ / 2)) :
    ContDiff ℝ ∞ (periodize hℓ g) := by
  rw [contDiff_iff_contDiffAt]
  intro z₀
  set n := toIcoDiv hℓ (-(ℓ / 2)) z₀.1
  have hx₀ : z₀.1 - n • ℓ ∈ Ico (-(ℓ / 2)) (-(ℓ / 2) + ℓ) := by
    rw [self_sub_toIcoDiv_zsmul]
    exact toIcoMod_mem_Ico _ _ _
  set Ψ : Plane → ℝ := fun z =>
    g (z.1 - n • ℓ - ℓ, z.2) + g (z.1 - n • ℓ, z.2) + g (z.1 - n • ℓ + ℓ, z.2)
  have hΨ : ContDiff ℝ ∞ Ψ := by
    have h1 : ContDiff ℝ ∞ (fun z : Plane => g (z.1 - n • ℓ - ℓ, z.2)) :=
      hgs.comp (((contDiff_fst.sub contDiff_const).sub contDiff_const).prodMk contDiff_snd)
    have h2 : ContDiff ℝ ∞ (fun z : Plane => g (z.1 - n • ℓ, z.2)) :=
      hgs.comp ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd)
    have h3 : ContDiff ℝ ∞ (fun z : Plane => g (z.1 - n • ℓ + ℓ, z.2)) :=
      hgs.comp (((contDiff_fst.sub contDiff_const).add contDiff_const).prodMk contDiff_snd)
    exact (h1.add h2).add h3
  have hopen : IsOpen {z : Plane | z.1 - n • ℓ ∈ Ioo (-(3 * ℓ / 2)) (3 * ℓ / 2)} :=
    isOpen_Ioo.preimage (continuous_fst.sub continuous_const)
  have hmem : z₀ ∈ {z : Plane | z.1 - n • ℓ ∈ Ioo (-(3 * ℓ / 2)) (3 * ℓ / 2)} := by
    obtain ⟨h1, h2⟩ := hx₀
    exact ⟨by linarith, by linarith⟩
  have hev : periodize hℓ g =ᶠ[𝓝 z₀] Ψ := by
    filter_upwards [hopen.mem_nhds hmem] with z hz
    exact periodize_eq_local hℓ hg n z hz
  exact hΨ.contDiffAt.congr_of_eventuallyEq hev

theorem periodize_eq_on_cell {ℓ : ℝ} (hℓ : 0 < ℓ) (g : Plane → ℝ) {z : Plane}
    (hz : z ∈ cell ℓ) : periodize hℓ g z = g z := by
  have h := (mem_prod.1 hz).1
  have hmod : toIcoMod hℓ (-(ℓ / 2)) z.1 = z.1 :=
    (toIcoMod_eq_self hℓ).2 ⟨le_of_lt h.1, by linarith [h.2]⟩
  simp [periodize, hmod]

/-- A smooth function with compact support inside the open cell periodizes to a periodic
test function that agrees with it on the cell. -/
theorem isPeriodicTest_periodize {ℓ : ℝ} (hℓ : 0 < ℓ) {g : Plane → ℝ}
    (hgs : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (hsub : tsupport g ⊆ cell ℓ) :
    IsPeriodicTest ℓ (periodize hℓ g) := by
  have hg : ∀ w : Plane, g w ≠ 0 → w.1 ∈ Ioo (-(ℓ / 2)) (ℓ / 2) := fun w hw =>
    (mem_prod.1 (hsub (subset_tsupport g hw))).1
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Plane)).1 hgc.isCompact.isBounded
  refine ⟨contDiff_periodize hℓ hgs hg, fun q η => ?_, R, fun z hz => ?_⟩
  · simp [periodize, toIcoMod_add_right]
  · by_contra hne
    have hmem := hR (subset_tsupport g hne)
    rw [Metric.mem_closedBall, dist_zero_right] at hmem
    have := norm_snd_le (toIcoMod hℓ (-(ℓ / 2)) z.1, z.2)
    rw [Real.norm_eq_abs] at this
    linarith

/-- Elements of `X_m` are locally integrable for `dq dη` on the cell. -/
theorem locallyIntegrable_X (ℓ m : ℝ) (f : X ℓ m) :
    LocallyIntegrable (f : Plane → ℝ) (cellMeasure ℓ) := by
  rw [locallyIntegrable_iff]
  intro K hK
  have hmem : MemLp (K.indicator fun _ => (1 : ℝ)) 2 (weightMeasure ℓ (-m)) := by
    apply memLp_weight_of_le_indicator ℓ (-m)
      (aestronglyMeasurable_const.indicator hK.measurableSet) hK 1
    intro z _
    by_cases hz : z ∈ K <;> simp [hz]
  have hint := integrable_mul_X ℓ m f (hmem.toLp _)
  rw [← integrable_indicator_iff hK.measurableSet]
  refine hint.congr ?_
  filter_upwards [ae_cell_of_ae_weight hmem.coeFn_toLp] with z hz
  rw [hz]
  by_cases hzK : z ∈ K <;> simp [hzK]

/-- An element of `X_m` that annihilates every periodic test function is zero. -/
theorem eq_zero_of_forall_test {ℓ m : ℝ} (hℓ : 0 < ℓ) (f : X ℓ m)
    (h : ∀ φ : Plane → ℝ, IsPeriodicTest ℓ φ → ∫ z, f z * φ z ∂(cellMeasure ℓ) = 0) :
    f = 0 := by
  have hzero := (isOpen_cell ℓ).ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((locallyIntegrable_X ℓ m f).locallyIntegrableOn (cell ℓ)) (fun g hgs hgc hsub => by
      rw [← h _ (isPeriodicTest_periodize hℓ hgs hgc hsub)]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (measurableSet_cell ℓ)] with z hz
      rw [periodize_eq_on_cell hℓ g hz, smul_eq_mul, mul_comm])
  apply Lp.ext
  refine ae_weight_of_ae_cell ?_
  filter_upwards [hzero, ae_restrict_mem (measurableSet_cell ℓ),
    ae_cell_of_ae_weight (Lp.coeFn_zero ℝ 2 (weightMeasure ℓ m))] with z h1 h2 h3
  rw [h1 h2, h3, Pi.zero_apply]

/-- Periodic weak derivatives are unique as elements of `X_m`. -/
theorem HasWeakDeriv.unique {ℓ m : ℝ} (hℓ : 0 < ℓ) {α : ℕ × ℕ} {f g g' : X ℓ m}
    (h : HasWeakDeriv ℓ m α f g) (h' : HasWeakDeriv ℓ m α f g') : g = g' := by
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_test hℓ
  intro φ hφ
  have e := (h φ hφ).symm.trans (h' φ hφ)
  have hs : ((-1 : ℝ) ^ (α.1 + α.2)) ≠ 0 := pow_ne_zero _ (by norm_num)
  have e' := mul_left_cancel₀ hs e
  have hi := integrable_mul_contBdd ℓ m g φ hφ.isContBdd
  have hi' := integrable_mul_contBdd ℓ m g' φ hφ.isContBdd
  calc ∫ z, (g - g') z * φ z ∂(cellMeasure ℓ)
      = ∫ z, (g z * φ z - g' z * φ z) ∂(cellMeasure ℓ) := by
        apply integral_congr_ae
        filter_upwards [ae_cell_of_ae_weight (Lp.coeFn_sub g g')] with z hz
        rw [hz, Pi.sub_apply, sub_mul]
    _ = 0 := by rw [integral_sub hi hi', e', sub_self]

/-! ### `H^k_m` as a closed weak-derivative graph -/

/-- Multi-indices `α = (α_q, α_η)` with `|α| = α_q + α_η ≤ k`. -/
def multiIndices (k : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (k + 1) ×ˢ Finset.range (k + 1)).filter fun α => α.1 + α.2 ≤ k

theorem mem_multiIndices {k : ℕ} {α : ℕ × ℕ} : α ∈ multiIndices k ↔ α.1 + α.2 ≤ k := by
  simp only [multiIndices, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

/-- The finite type of multi-indices of order at most `k`. -/
abbrev MultiIdx (k : ℕ) := ↥(multiIndices k)

/-- The zero multi-index, whose slot stores the function itself. -/
def zeroIdx (k : ℕ) : MultiIdx k := ⟨(0, 0), mem_multiIndices.2 (by simp)⟩

/-- The Hilbert sum `⊕_{|α| ≤ k} X_m` with the square-sum norm. -/
abbrev HkAmbient (ℓ m : ℝ) (k : ℕ) := PiLp 2 (fun _ : MultiIdx k => X ℓ m)

/-- The periodic tests, as a type. -/
abbrev TestFn (ℓ : ℝ) := {φ : Plane → ℝ // IsPeriodicTest ℓ φ}

/-- The continuous constraint `F ↦ ∫ F_0 D^α φ - (-1)^{|α|} ∫ F_α φ` on the ambient sum. -/
def constraint (ℓ m : ℝ) (k : ℕ) (α : MultiIdx k) (φ : TestFn ℓ) :
    HkAmbient ℓ m k →L[ℝ] ℝ :=
  (dualX ℓ m (ofContBdd ℓ (-m) _ (φ.2.partialMulti_isContBdd α.1))).comp
      (PiLp.proj 2 (fun _ : MultiIdx k => X ℓ m) (zeroIdx k)) -
    ((-1 : ℝ) ^ (α.1.1 + α.1.2)) •
      (dualX ℓ m (ofContBdd ℓ (-m) _ φ.2.isContBdd)).comp
        (PiLp.proj 2 (fun _ : MultiIdx k => X ℓ m) α)

theorem constraint_apply (ℓ m : ℝ) (k : ℕ) (α : MultiIdx k) (φ : TestFn ℓ)
    (F : HkAmbient ℓ m k) :
    constraint ℓ m k α φ F =
      ∫ z, F.ofLp (zeroIdx k) z * partialMulti α.1 φ.1 z ∂(cellMeasure ℓ) -
        (-1) ^ (α.1.1 + α.1.2) * ∫ z, F.ofLp α z * φ.1 z ∂(cellMeasure ℓ) := by
  simp only [constraint, sub_apply, smul_apply,
    ContinuousLinearMap.comp_apply, PiLp.proj_apply, smul_eq_mul]
  rw [dualX_ofContBdd, dualX_ofContBdd]

/-- The weighted periodic Sobolev graph: tuples `(D^α f)_{|α| ≤ k}` in `⊕ X_m` satisfying
every weak-derivative identity. -/
def HkSub (ℓ m : ℝ) (k : ℕ) : Submodule ℝ (HkAmbient ℓ m k) :=
  ⨅ (α : MultiIdx k) (φ : TestFn ℓ),
    LinearMap.ker (constraint ℓ m k α φ : HkAmbient ℓ m k →ₗ[ℝ] ℝ)

theorem mem_HkSub_iff (ℓ m : ℝ) (k : ℕ) (F : HkAmbient ℓ m k) :
    F ∈ HkSub ℓ m k ↔
      ∀ α : MultiIdx k, HasWeakDeriv ℓ m α.1 (F.ofLp (zeroIdx k)) (F.ofLp α) := by
  simp only [HkSub, Submodule.mem_iInf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    constraint_apply, sub_eq_zero]
  constructor
  · intro h α φ hφ
    exact h α ⟨φ, hφ⟩
  · intro h α φ
    exact h α φ.1 φ.2

theorem isClosed_HkSub (ℓ m : ℝ) (k : ℕ) : IsClosed (HkSub ℓ m k : Set (HkAmbient ℓ m k)) := by
  rw [HkSub, Submodule.coe_iInf]
  refine isClosed_iInter fun α => ?_
  rw [Submodule.coe_iInf]
  exact isClosed_iInter fun φ => (constraint ℓ m k α φ).isClosed_ker

/-- `H^k_m = {f : D^α f ∈ X_m, |α| ≤ k}` (`paper/main.tex`, line 13882), a real Hilbert
space with norm `(∑_{|α| ≤ k} ‖D^α f‖²_{X_m})^{1/2}`. -/
abbrev Hk (ℓ m : ℝ) (k : ℕ) := ↥(HkSub ℓ m k)

instance Hk_completeSpace (ℓ m : ℝ) (k : ℕ) : CompleteSpace (Hk ℓ m k) :=
  (isClosed_HkSub ℓ m k).completeSpace_coe

example (ℓ m : ℝ) (k : ℕ) : InnerProductSpace ℝ (Hk ℓ m k) := inferInstance

/-- `H^{-k}_m = (H^k_{-m})^*` (`paper/main.tex`, lines 13887–13888), the strong dual of the Hilbert
space `H^k_{-m}`. -/
abbrev Hneg (ℓ m : ℝ) (k : ℕ) := StrongDual ℝ (Hk ℓ (-m) k)

namespace Hk

variable {ℓ m : ℝ} {k : ℕ}

/-- The function `f ∈ X_m`. -/
def value (F : Hk ℓ m k) : X ℓ m := (F : HkAmbient ℓ m k).ofLp (zeroIdx k)

/-- Its weak derivative `D^α f ∈ X_m`. -/
def deriv (F : Hk ℓ m k) (α : MultiIdx k) : X ℓ m := (F : HkAmbient ℓ m k).ofLp α

theorem hasWeakDeriv (F : Hk ℓ m k) (α : MultiIdx k) :
    HasWeakDeriv ℓ m α.1 F.value (F.deriv α) :=
  (mem_HkSub_iff ℓ m k F).1 F.2 α

theorem deriv_zeroIdx (F : Hk ℓ m k) : F.deriv (zeroIdx k) = F.value := rfl

/-- The `H^k_m` norm is the square-sum of the `X_m` norms of all derivatives of order `≤ k`. -/
theorem norm_sq (F : Hk ℓ m k) : ‖F‖ ^ 2 = ∑ α : MultiIdx k, ‖F.deriv α‖ ^ 2 := by
  change ‖(F : HkAmbient ℓ m k)‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2]
  rfl

/-- An element of `H^k_m` is determined by its value: its derivatives are the unique weak
derivatives. -/
theorem value_injective (hℓ : 0 < ℓ) : Function.Injective (value : Hk ℓ m k → X ℓ m) := by
  intro F G hv
  have hd : ∀ α : MultiIdx k, F.deriv α = G.deriv α := fun α => by
    have hG := G.hasWeakDeriv α
    rw [← hv] at hG
    exact (F.hasWeakDeriv α).unique hℓ hG
  apply Subtype.ext
  apply (WithLp.ext_iff (p := 2)).2
  funext α
  exact hd α

end Hk

/-- **`H^k_m` is the space of the manuscript.** For `ℓ > 0`, `f ∈ X_m` is the value of an
element of `H^k_m` exactly when every weak derivative `D^α f`, `|α| ≤ k`, exists in `X_m`
(`paper/main.tex`, line 13882). The element is then unique (`Hk.value_injective`). -/
theorem mem_range_value_iff (ℓ m : ℝ) (k : ℕ) (f : X ℓ m) :
    f ∈ Set.range (Hk.value : Hk ℓ m k → X ℓ m) ↔
      ∀ α : ℕ × ℕ, α.1 + α.2 ≤ k → ∃ g : X ℓ m, HasWeakDeriv ℓ m α f g := by
  constructor
  · rintro ⟨F, rfl⟩ α hα
    exact ⟨F.deriv ⟨α, mem_multiIndices.2 hα⟩, F.hasWeakDeriv ⟨α, mem_multiIndices.2 hα⟩⟩
  · intro h
    classical
    let G : MultiIdx k → X ℓ m := fun α =>
      if α.1 = (0, 0) then f else Classical.choose (h α.1 (mem_multiIndices.1 α.2))
    have hG0 : G (zeroIdx k) = f := by simp [G, zeroIdx]
    have hmem : WithLp.toLp 2 G ∈ HkSub ℓ m k := by
      rw [mem_HkSub_iff]
      intro α
      change HasWeakDeriv ℓ m α.1 (G (zeroIdx k)) (G α)
      rw [hG0]
      by_cases hα : α.1 = (0, 0)
      · have : G α = f := by simp [G, hα]
        rw [this, hα]
        exact hasWeakDeriv_zero ℓ m f
      · have : G α = Classical.choose (h α.1 (mem_multiIndices.1 α.2)) := by simp [G, hα]
        rw [this]
        exact Classical.choose_spec (h α.1 (mem_multiIndices.1 α.2))
    exact ⟨⟨WithLp.toLp 2 G, hmem⟩, hG0⟩

end UnforcedLeray.B0656
