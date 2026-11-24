import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3

/-!
# Part III-a, `PartIII-a:T18/3/1/3/3` (`MollLimit`): the limit `k → ∞` of the mollified identity

Source of record: `the November 2 reference manuscript` (SP) lines 3427-3440 (the
energy class: `b ∈ L²_loc((0,∞); L²)`, `∇b ∈ L²_loc((0,∞); L²)`) and 3541-3552 (the energy
identity, used on `[δ_j, B]`). The energy identity for the energy class is obtained by mollifying
in `x`, writing the energy identity for `u_k = J_k b` (`MollifiedEnergyIdentity`) and letting
`k → ∞`; this file reduces the last step, `MollifiedEnergyLimit`, to finer statements.

Proved here:
* `lmMoll_pd_eq`: for `f ∈ L²(cell)` with weak gradient columns `g j ∈ L²(cell)`,
  `∂_j (J_k f)_i = (J_k g_j)_i` pointwise (`IsLMMollifier.commute`);
* `lmMoll_pd2_eq`: the same for `J_k J_k f`, `∂_j (J_k J_k f)_i = (J_k J_k g_j)_i`, from
  `LMSmoothWeakPd` (the classical derivative of the smooth periodic `L²` field `J_k f` is weak);
* `mollifiedEnergyLimit_of`: `MollifiedEnergyLimit` from the Props below, by dominated convergence
  in `s` against `w'` and `w`.

The Props (one task each):
* `LMMollPointwiseE/N/R`: for a good slice `s` (`LMGoodSlice`: `b(s)`, the columns of `G(s)` and
  of `F(s)` in `L²(cell)`), `E_k(s) → E(s)`, `N_k(s) → N(s)`, `R_k(s) → R(s)`;
* `LMMollDomEN`, `LMMollDomR`: for a good slice, `0 ≤ E_k ≤ E`, `0 ≤ N_k ≤ N` (contraction) and
  `|R_k| ≤ N_F + N` (Cauchy-Schwarz and contraction twice), `N_F(s) = ∫_cell |F(s)|²`;
* `LMMollMeasurableEN`, `LMMollMeasurableR`: `s ↦ E_k(s), N_k(s), R_k(s)` are a.e. strongly
  measurable on `(0,∞)` (`IsLMMollifier.measurable`; for `N_k, R_k` after the a.e. identities
  `lmMoll_pd_eq`, `lmMoll_pd2_eq`);
* `LMAeGoodSlice`: a.e. `s > 0` is a good slice (Tonelli on `energyLoc`, `L2locTensor`);
* `LMEnergyLocInt`: `E`, `N` and `N_F` are integrable on every `[s₁, s₂] ⊂ (0,∞)`;
* `LMWeightedDCT`: dominated convergence against a continuous weight with compact support in
  `(0,∞)`, with a locally integrable dominating function.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- A good time slice `s`: `b(s)`, every column `G(s)_{·j}` of the weak gradient and every column
`F(s)_{·j}` of the force lie in `L²(cell)` (SP 3427-3440: the energy class; this holds for a.e.
`s > 0`, `LMAeGoodSlice`). -/
def LMGoodSlice (c : ℝ) (F G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (s : ℝ) : Prop :=
  LMCellL2 c (fun y => b (s, y)) ∧ (∀ j : Fin 2, LMCellL2 c (fun y i => G (s, y) i j)) ∧
    ∀ j : Fin 2, LMCellL2 c (fun y i => F (s, y) i j)

/-- **Gradient of a mollified field**: if `f ∈ L²(cell)` has weak derivatives `∂_j f_i = (g j)_i`
in `L²(cell)` (in the sense of `HasWeakCellDerivC`, e.g. `b(s)` and `G(s)` by
`IsCausalEnergySolution.weakGrad`), then `∂_j (J_k f)_i = (J_k g_j)_i` pointwise. -/
theorem lmMoll_pd_eq {c : ℝ} {J : ℕ → LMSpField → LMSpField} (hJ : IsLMMollifier c J)
    {f : LMSpField} {g : Fin 2 → LMSpField} (hf : LMCellL2 c f) (hg : ∀ j, LMCellL2 c (g j))
    (hfg : ∀ i j, HasWeakCellDerivC c j (fun x => f x i) (fun x => g j x i))
    (k : ℕ) (i j : Fin 2) (x : ℝ × ℝ) :
    LMPd j (fun y => J k f y i) x = J k (g j) x i :=
  hJ.commute k f (g j) j hf (hg j)
    (fun i' => ⟨hf i', hg j i', fun φ hφ hper hR => (hfg i' j).2 φ ⟨hφ, hper, hR⟩⟩) i x

/-- **Gradient of a twice mollified field**: under the hypotheses of `lmMoll_pd_eq`,
`∂_j (J_k J_k f)_i = (J_k J_k g_j)_i` pointwise. The smooth periodic field `J_k f` has the classical
derivative `J_k g_j ∈ L²(cell)`, which is a weak derivative by `LMSmoothWeakPd`; apply `commute`
again. -/
theorem lmMoll_pd2_eq (hS : LMSmoothWeakPd) {c : ℝ} (hc : 0 < c)
    {J : ℕ → LMSpField → LMSpField} (hJ : IsLMMollifier c J)
    {f : LMSpField} {g : Fin 2 → LMSpField} (hf : LMCellL2 c f) (hg : ∀ j, LMCellL2 c (g j))
    (hfg : ∀ i j, HasWeakCellDerivC c j (fun x => f x i) (fun x => g j x i))
    (k : ℕ) (i j : Fin 2) (x : ℝ × ℝ) :
    LMPd j (fun y => J k (J k f) y i) x = J k (J k (g j)) x i := by
  refine hJ.commute k (J k f) (J k (g j)) j (hJ.memL2 k f hf) (hJ.memL2 k _ (hg j))
    (fun i' => ?_) i x
  have h2 : LMPd j (fun y => J k f y i') = fun x => J k (g j) x i' :=
    funext fun x => lmMoll_pd_eq hJ hf hg hfg k i' j x
  have h1 := hS c hc j (fun y => J k f y i') (hJ.smooth k f hf i')
    (fun x => hJ.periodic k f hf x i') (hJ.memL2 k f hf i')
    (by rw [h2]; exact hJ.memL2 k (g j) (hg j) i')
  rwa [h2] at h1

/-- **Pointwise limit of `E_k`** (SP 3541-3552, `k → ∞`): on a good slice,
`E_k(s) = ∫_cell |J_k b(s)|² → E(s) = ∫_cell |b(s)|²` (`IsLMMollifier.tendsto`, `memL2`). -/
def LMMollPointwiseE : Prop :=
  ∀ (c ν : ℝ) (μ : ℂ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ),
    FreeSolData c ν μ F b G → ∀ J : ℕ → LMSpField → LMSpField, IsLMMollifier c J →
    ∀ s : ℝ, 0 < s → LMGoodSlice c F G b s →
      Tendsto (fun k : ℕ => LMMollE c J b k s) atTop (𝓝 (energyE c b s))

/-- **Pointwise limit of `N_k`**: on a good slice, `N_k(s) = ∫_cell |∇J_k b(s)|² → N(s)`
(`∇J_k b(s) = J_k G(s)` by `lmMoll_pd_eq`, then `J_k G(s)_{·j} → G(s)_{·j}` in `L²(cell)`). -/
def LMMollPointwiseN : Prop :=
  ∀ (c ν : ℝ) (μ : ℂ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ),
    FreeSolData c ν μ F b G → ∀ J : ℕ → LMSpField → LMSpField, IsLMMollifier c J →
    ∀ s : ℝ, 0 < s → LMGoodSlice c F G b s →
      Tendsto (fun k : ℕ => LMMollN c J b k s) atTop (𝓝 (energyN c G s))

/-- **Pointwise limit of `R_k`**: on a good slice, `R_k(s) = ∫_cell Re⟨F(s), ∇J_k² b(s)⟩ → R(s)`
(`∇J_k² b(s) = J_k² G(s)` by `lmMoll_pd2_eq`, `J_k² G(s) → G(s)` in `L²(cell)`, Cauchy-Schwarz). -/
def LMMollPointwiseR : Prop :=
  ∀ (c ν : ℝ) (μ : ℂ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ),
    FreeSolData c ν μ F b G → ∀ J : ℕ → LMSpField → LMSpField, IsLMMollifier c J →
    ∀ s : ℝ, 0 < s → LMGoodSlice c F G b s →
      Tendsto (fun k : ℕ => LMMollR c J F b k s) atTop (𝓝 (energyR c F G s))

/-- **Domination of `E_k`, `N_k`**: on a good slice, `0 ≤ E_k(s) ≤ E(s)` and `0 ≤ N_k(s) ≤ N(s)`
(`IsLMMollifier.contr`, for `N_k` columnwise after `lmMoll_pd_eq`). -/
def LMMollDomEN : Prop :=
  ∀ (c ν : ℝ) (μ : ℂ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ),
    FreeSolData c ν μ F b G → ∀ J : ℕ → LMSpField → LMSpField, IsLMMollifier c J →
    ∀ s : ℝ, 0 < s → LMGoodSlice c F G b s → ∀ k : ℕ,
      0 ≤ LMMollE c J b k s ∧ LMMollE c J b k s ≤ energyE c b s ∧
        0 ≤ LMMollN c J b k s ∧ LMMollN c J b k s ≤ energyN c G s

/-- **Domination of `R_k`**: on a good slice, `|R_k(s)| ≤ ∫_cell |F(s)|² + N(s)`
(`|Re⟨F, J_k² G⟩| ≤ |F|² + |J_k² G|²` pointwise, then `contr` twice columnwise). -/
def LMMollDomR : Prop :=
  ∀ (c ν : ℝ) (μ : ℂ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ),
    FreeSolData c ν μ F b G → ∀ J : ℕ → LMSpField → LMSpField, IsLMMollifier c J →
    ∀ s : ℝ, 0 < s → LMGoodSlice c F G b s → ∀ k : ℕ,
      |LMMollR c J F b k s| ≤ energyN c F s + energyN c G s

/-- **Measurability of `E_k`, `N_k` in `s`** on `(0,∞)` (`IsLMMollifier.measurable`,
`StronglyMeasurable.integral_prod_right'`; for `N_k` on the a.e. set of good slices, where
`N_k(s) = ∫_cell |J_k G(s)|²` by `lmMoll_pd_eq`). -/
def LMMollMeasurableEN : Prop :=
  ∀ (c ν : ℝ) (μ : ℂ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ),
    FreeSolData c ν μ F b G → ∀ J : ℕ → LMSpField → LMSpField, IsLMMollifier c J → ∀ k : ℕ,
      AEStronglyMeasurable (fun s => LMMollE c J b k s) (volume.restrict (Ioi (0 : ℝ))) ∧
        AEStronglyMeasurable (fun s => LMMollN c J b k s) (volume.restrict (Ioi (0 : ℝ)))

/-- **Measurability of `R_k` in `s`** on `(0,∞)` (on good slices
`R_k(s) = ∫_cell Re⟨F(s), J_k² G(s)⟩` by `lmMoll_pd2_eq`; `IsLMMollifier.measurable` twice). -/
def LMMollMeasurableR : Prop :=
  ∀ (c ν : ℝ) (μ : ℂ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ),
    FreeSolData c ν μ F b G → ∀ J : ℕ → LMSpField → LMSpField, IsLMMollifier c J → ∀ k : ℕ,
      AEStronglyMeasurable (fun s => LMMollR c J F b k s) (volume.restrict (Ioi (0 : ℝ)))

/-- **Almost every slice is good** (SP 3427-3440: `b, ∇b ∈ L²_loc((0,∞); L²)`, `F ∈ L²_loc`):
Tonelli on `IsCausalEnergySolution.energyLoc` and `L2locTensor` over `[s₁, s₂] × cell`, and a
countable union of the intervals `[1/(n+1), n+1]`. -/
def LMAeGoodSlice : Prop :=
  ∀ (c ν : ℝ) (μ : ℂ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ),
    FreeSolData c ν μ F b G → ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), LMGoodSlice c F G b s

/-- **Local integrability of the energies** (SP 3427-3440): `E`, `N` and `N_F = ∫_cell |F|²` are
integrable on every `[s₁, s₂] ⊂ (0,∞)` (Tonelli on `energyLoc`, `L2locTensor`). -/
def LMEnergyLocInt : Prop :=
  ∀ (c ν : ℝ) (μ : ℂ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ),
    FreeSolData c ν μ F b G → ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      IntegrableOn (fun s => energyE c b s) (Icc s₁ s₂) ∧
        IntegrableOn (fun s => energyN c G s) (Icc s₁ s₂) ∧
        IntegrableOn (fun s => energyN c F s) (Icc s₁ s₂)

/-- **Dominated convergence against a weight with compact support in `(0,∞)`**: the dominating
function `g` need only be integrable on compact intervals `[s₁, s₂] ⊂ (0,∞)`. -/
def LMWeightedDCT : Prop :=
  ∀ wt : ℝ → ℝ, Continuous wt → HasCompactSupport wt → tsupport wt ⊆ Ioi (0 : ℝ) →
    ∀ (f : ℕ → ℝ → ℝ) (f₀ g : ℝ → ℝ),
      (∀ k, AEStronglyMeasurable (f k) (volume.restrict (Ioi (0 : ℝ)))) →
      (∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ → IntegrableOn g (Icc s₁ s₂)) →
      (∀ k, ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), |f k s| ≤ g s) →
      (∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), Tendsto (fun k => f k s) atTop (𝓝 (f₀ s))) →
      Tendsto (fun k => ∫ s in Ioi (0 : ℝ), wt s * f k s) atTop
        (𝓝 (∫ s in Ioi (0 : ℝ), wt s * f₀ s))

/-- **The limit of the mollified identity**, from the Props above: dominated convergence against
`w'` (dominated by `E`) and against `w` (dominated by `2|Re μ| s⁻¹ E + 2ν N + 2(N_F + N)`). -/
theorem mollifiedEnergyLimit_of (hPE : LMMollPointwiseE) (hPN : LMMollPointwiseN)
    (hPR : LMMollPointwiseR) (hDEN : LMMollDomEN) (hDR : LMMollDomR)
    (hMEN : LMMollMeasurableEN) (hMR : LMMollMeasurableR) (hAe : LMAeGoodSlice)
    (hLoc : LMEnergyLocInt) (hDCT : LMWeightedDCT) : MollifiedEnergyLimit := by
  intro c ν μ F b G hD J hJ w hw hcs hts
  have hgood : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), 0 < s ∧ LMGoodSlice c F G b s := by
    filter_upwards [hAe c ν μ F b G hD, ae_restrict_mem measurableSet_Ioi] with s h1 h2
    exact ⟨h2, h1⟩
  refine ⟨?_, ?_⟩
  · refine hDCT (deriv w) (hw.continuous_deriv (by simp)) hcs.deriv
      (tsupport_deriv_subset.trans hts) (fun k s => LMMollE c J b k s) (energyE c b)
      (energyE c b) (fun k => (hMEN c ν μ F b G hD J hJ k).1)
      (fun s₁ s₂ h0 h12 => (hLoc c ν μ F b G hD s₁ s₂ h0 h12).1) (fun k => ?_) ?_
    · filter_upwards [hgood] with s hs
      obtain ⟨h0, h1, -, -⟩ := hDEN c ν μ F b G hD J hJ s hs.1 hs.2 k
      show |LMMollE c J b k s| ≤ energyE c b s
      rw [abs_of_nonneg h0]
      exact h1
    · filter_upwards [hgood] with s hs
      exact hPE c ν μ F b G hD J hJ s hs.1 hs.2
  · refine hDCT w hw.continuous hcs hts
      (fun k s => 2 * μ.re / s * LMMollE c J b k s + 2 * ν * LMMollN c J b k s +
        2 * LMMollR c J F b k s)
      (fun s => 2 * μ.re / s * energyE c b s + 2 * ν * energyN c G s + 2 * energyR c F G s)
      (fun s => 2 * |μ.re| / s * energyE c b s + 2 * ν * energyN c G s +
        2 * (energyN c F s + energyN c G s)) (fun k => ?_) (fun s₁ s₂ h0 h12 => ?_)
      (fun k => ?_) ?_
    · obtain ⟨hE, hN⟩ := hMEN c ν μ F b G hD J hJ k
      have hR := hMR c ν μ F b G hD J hJ k
      have hq : Measurable fun s : ℝ => 2 * μ.re / s := measurable_const.div measurable_id
      exact ((hq.aestronglyMeasurable.mul hE).add (aestronglyMeasurable_const.mul hN)).add
        (aestronglyMeasurable_const.mul hR)
    · obtain ⟨hE, hN, hF⟩ := hLoc c ν μ F b G hD s₁ s₂ h0 h12
      have hcont : ContinuousOn (fun s : ℝ => 2 * |μ.re| / s) (Icc s₁ s₂) :=
        continuousOn_const.div continuousOn_id (fun s hs => (h0.trans_le hs.1).ne')
      have h1 : IntegrableOn (fun s => 2 * |μ.re| / s * energyE c b s) (Icc s₁ s₂) :=
        hE.continuousOn_mul hcont isCompact_Icc
      exact Integrable.add (Integrable.add h1 (Integrable.const_mul hN (2 * ν)))
        (Integrable.const_mul (Integrable.add hF hN) 2)
    · filter_upwards [hgood] with s hs
      obtain ⟨hE0, hE1, hN0, hN1⟩ := hDEN c ν μ F b G hD J hJ s hs.1 hs.2 k
      have hR1 := hDR c ν μ F b G hD J hJ s hs.1 hs.2 k
      have hν : 0 ≤ 2 * ν := by linarith [hD.pos_ν]
      have e1 : |2 * μ.re / s * LMMollE c J b k s| ≤ 2 * |μ.re| / s * energyE c b s := by
        rw [abs_mul, abs_div, abs_mul, abs_two, abs_of_pos hs.1, abs_of_nonneg hE0]
        exact mul_le_mul_of_nonneg_left hE1 (div_nonneg (by positivity) hs.1.le)
      have e2 : |2 * ν * LMMollN c J b k s| ≤ 2 * ν * energyN c G s := by
        rw [abs_of_nonneg (mul_nonneg hν hN0)]
        exact mul_le_mul_of_nonneg_left hN1 hν
      have e3 : |2 * LMMollR c J F b k s| ≤ 2 * (energyN c F s + energyN c G s) := by
        rw [abs_mul, abs_two]
        exact mul_le_mul_of_nonneg_left hR1 (by norm_num)
      show |2 * μ.re / s * LMMollE c J b k s + 2 * ν * LMMollN c J b k s +
          2 * LMMollR c J F b k s| ≤ 2 * |μ.re| / s * energyE c b s + 2 * ν * energyN c G s +
          2 * (energyN c F s + energyN c G s)
      linarith [abs_add_le (2 * μ.re / s * LMMollE c J b k s + 2 * ν * LMMollN c J b k s)
          (2 * LMMollR c J F b k s),
        abs_add_le (2 * μ.re / s * LMMollE c J b k s) (2 * ν * LMMollN c J b k s)]
    · filter_upwards [hgood] with s hs
      exact (((hPE c ν μ F b G hD J hJ s hs.1 hs.2).const_mul (2 * μ.re / s)).add
        ((hPN c ν μ F b G hD J hJ s hs.1 hs.2).const_mul (2 * ν))).add
        ((hPR c ν μ F b G hD J hJ s hs.1 hs.2).const_mul 2)

end UnforcedLeray.Short.IIIa
