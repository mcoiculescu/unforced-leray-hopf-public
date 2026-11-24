import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_4_3
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous

/-!
# Part II-b, task `PartII-b:T13/1/4/3/3` (`chmMollConv`): decomposition

Source: `the November 2 reference manuscript` lines 1933-1935 (smooth periodic
approximation: `‖ρ_n ⋆ g - g‖ ≤ ∫ ρ_n(y) ‖g(· - y) - g‖ dy`, then continuity of translation in
`L^r(cylMeas c)` for `q`-periodic `g`).

Route: (`ChmMink`) Minkowski's integral inequality in `L^r(cylMeas c)`; (`ChmWinMemLp`) the
truncation of a `q`-periodic `g ∈ L^r(cylMeas c)` to a `q`-window of finite width is in
`L^r(volume)` (by `q`-periodicity the window is a finite union of translated cells);
(`ChmWinReduce`) on the cell, small translates of `g` agree with those of the truncation, and
`cylMeas c ≤ c⁻¹ • volume`; continuity of translation in `L^r(volume)` (proved here).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

/-- The truncation of `g` to the `q`-window `|q| ≤ R`. -/
def chmWinR (R : ℝ) (g : Coord → ℂ) : Coord → ℂ := fun x => if |x.2.1| ≤ R then g x else 0

/-- **Lemma A (Minkowski).** For a continuous compactly supported kernel `ρ` with `∫ ρ = 1` and a
locally integrable `g`: `‖ρ ⋆ g - g‖ ≤ ∫ ρ(y) ‖g(· - y) - g‖ dy` in `L^r(cylMeas c)`
(write `ρ ⋆ g - g = ∫ ρ(y)(g(· - y) - g(·)) dy`, then
`PlanarBS.Conv.eLpNorm_integral_le` from `Lib/Kernels/PlanarBS/P/Infra/ConvMinkowski/Minkowski.lean`
for the measures `cylMeas c` and `volume`; `cylMeas c ≪ volume`, the map `(x, y) ↦ x - y` is quasi
measure preserving). -/
def ChmMink : Prop :=
  ∀ r : ℝ, 1 ≤ r → ∀ c : ℝ, 0 < c → ∀ (ρ : Coord → ℝ) (g : Coord → ℂ),
    Continuous ρ → HasCompactSupport ρ → ∫ y, ρ y = 1 →
    LocallyIntegrable g volume →
    cylNorm c r (fun x => chmConv ρ g x - g x) ≤
      ∫⁻ y, ENNReal.ofReal |ρ y| * cylNorm c r (fun x => g (x - y) - g x)

/-- **Lemma B1 (periodic window).** A `q`-periodic strongly measurable `g ∈ L^r(cylMeas c)` is in
`L^r(volume)` after truncation to `|q| ≤ R`: the window `{|q| ≤ R}` is covered by `2K+1` translates
`cell + k c e_q` (`K = ⌈R/c⌉ + 1`), on each of which `∫ |g|^r d(ds dq dη)` equals
`c ∫ |g|^r d(cylMeas c)` by `QPeriodicS` (a.e. `g ∘ qShift c = g`, hence for `qShift (k c)`;
`volume` is invariant under `qShift`; `Cyl.lintegral_cell_comp_add` in `Lib/Cylinder/Basic.lean`). -/
def ChmWinMemLp : Prop :=
  ∀ r : ℝ, 1 ≤ r → ∀ c : ℝ, 0 < c → ∀ g : Coord → ℂ, QPeriodicS c g →
    AEStronglyMeasurable g volume → cylNorm c r g < ⊤ →
    ∀ R : ℝ, MemLp (chmWinR R g) (ENNReal.ofReal r) volume

/-- **Lemma B3 (reduction to the whole space).** For `‖y‖ ≤ 1`, `x` in the cell strip has
`x - y` in the window `|q| ≤ c/2 + 1`, so the translate differences of `g` and of its truncation
agree `cylMeas c`-a.e.; and `cylMeas c = c⁻¹ • volume.restrict (univ ×ˢ cell c)` is at most
`c⁻¹ • volume` (`eLpNorm_smul_measure_of_ne_top`, `eLpNorm_mono_measure`). -/
def ChmWinReduce : Prop :=
  ∀ r : ℝ, 1 ≤ r → ∀ c : ℝ, 0 < c → ∀ g : Coord → ℂ, ∀ y : Coord, ‖y‖ ≤ 1 →
    cylNorm c r (fun x => g (x - y) - g x) ≤
      ENNReal.ofReal c⁻¹ ^ (1 / r) *
        eLpNorm (fun x => chmWinR (c / 2 + 1) g (x - y) - chmWinR (c / 2 + 1) g x)
          (ENNReal.ofReal r) volume

/-- Properties of the mollifier `ρ_n`. -/
theorem chm_rho_props (n : ℕ) :
    Continuous (chmRho n) ∧ HasCompactSupport (chmRho n) ∧ (∀ y, 0 ≤ chmRho n y) ∧
      ∫ y, chmRho n y = 1 ∧ ∀ y : Coord, 1 / ((n : ℝ) + 2) < ‖y‖ → chmRho n y = 0 := by
  have hb : ∀ y : Coord, 1 / ((n : ℝ) + 2) < ‖y‖ → chmRho n y = 0 := by
    intro y hy
    unfold chmRho
    refine Function.notMem_support.mp ?_
    rw [ContDiffBump.support_normed_eq, Metric.mem_ball, dist_zero_right]
    simpa using hy.not_gt
  refine ⟨ContDiffBump.continuous_normed _, ContDiffBump.hasCompactSupport_normed _,
    fun y => ContDiffBump.nonneg_normed _ y, ContDiffBump.integral_normed _, hb⟩

/-- Continuity of translations in `L^p(volume)` on `Coord`, `p < ∞` (as `Sob.tendsto_eLpNorm_translate_sub`,
whose proof uses only that the measure is an additive Haar measure). -/
theorem chm_translate_tendsto {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) {f : Coord → ℂ}
    (hf : MemLp f p volume) :
    Tendsto (fun h : Coord => eLpNorm (fun y => f (y + h) - f y) p volume) (𝓝 0) (𝓝 0) := by
  have : Fact (p ≠ ⊤) := ⟨hp⟩
  set v : Lp ℂ p (volume : Measure Coord) := hf.toLp f
  have hc : Continuous fun h : Coord => (DomAddAct.mk h +ᵥ v : Lp ℂ p (volume : Measure Coord)) - v :=
    (continuous_vadd.comp (DomAddAct.continuous_mk.prodMk continuous_const)).sub
      continuous_const
  have h0 : (DomAddAct.mk (0 : Coord) +ᵥ v : Lp ℂ p (volume : Measure Coord)) - v = 0 := by
    rw [DomAddAct.mk_zero, zero_vadd, sub_self]
  have hlim := hc.tendsto 0
  rw [h0] at hlim
  have hlim' := (ENNReal.continuous_coe.tendsto _).comp
    ((continuous_nnnorm.tendsto (0 : Lp ℂ p (volume : Measure Coord))).comp hlim)
  simp only [nnnorm_zero, ENNReal.coe_zero] at hlim'
  refine hlim'.congr fun h => ?_
  simp only [Function.comp_apply]
  rw [← enorm_eq_nnnorm, Lp.enorm_def]
  refine eLpNorm_congr_ae ?_
  have hq : ∀ᵐ y ∂(volume : Measure Coord), v (h + y) = f (h + y) :=
    (measurePreserving_add_left (volume : Measure Coord) h).quasiMeasurePreserving.ae hf.coeFn_toLp
  filter_upwards [Lp.coeFn_sub (DomAddAct.mk h +ᵥ v) v, DomAddAct.vadd_Lp_ae_eq
    (DomAddAct.mk h) v, hf.coeFn_toLp, hq] with y h1 h2 h3 h4
  rw [h1, Pi.sub_apply, h2, h3]
  simp only [Equiv.symm_apply_apply, vadd_eq_add]
  rw [h4, add_comm]

theorem chm_transCont_of (hB1 : ChmWinMemLp) (hB3 : ChmWinReduce) (r : ℝ) (hr : 1 < r)
    (c : ℝ) (hc : 0 < c) (g : Coord → ℂ) (hp : QPeriodicS c g)
    (hm : AEStronglyMeasurable g volume) (hn : cylNorm c r g < ⊤) :
    Tendsto (fun y : Coord => cylNorm c r (fun x => g (x - y) - g x)) (𝓝 0) (𝓝 0) := by
  have hmem := hB1 r hr.le c hc g hp hm hn (c / 2 + 1)
  have : Fact (1 ≤ ENNReal.ofReal r) := ⟨ENNReal.one_le_ofReal.mpr hr.le⟩
  have hT := chm_translate_tendsto (p := ENNReal.ofReal r) ENNReal.ofReal_ne_top hmem
  have hneg : Tendsto (fun y : Coord => -y) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_neg (G := Coord)).tendsto 0
  have h2 := hT.comp hneg
  have hK : ENNReal.ofReal c⁻¹ ^ (1 / r) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by have : 0 < r := by linarith
                                      positivity) ENNReal.ofReal_ne_top
  have h3 := ENNReal.Tendsto.const_mul h2 (Or.inr hK)
  rw [mul_zero] at h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h3
    (Eventually.of_forall fun _ => zero_le) ?_
  have hball : ∀ᶠ y : Coord in 𝓝 0, ‖y‖ ≤ 1 := by
    have : Metric.closedBall (0 : Coord) 1 ∈ 𝓝 (0 : Coord) := Metric.closedBall_mem_nhds _ one_pos
    filter_upwards [this] with y hy using by simpa using hy
  filter_upwards [hball] with y hy
  have := hB3 r hr.le c hc g y hy
  simpa [Function.comp_def, sub_eq_add_neg] using this

theorem chm_locInt_of (hB1 : ChmWinMemLp) (r : ℝ) (hr : 1 < r)
    (c : ℝ) (hc : 0 < c) (g : Coord → ℂ) (hp : QPeriodicS c g)
    (hm : AEStronglyMeasurable g volume) (hn : cylNorm c r g < ⊤) :
    LocallyIntegrable g volume := by
  intro x
  set R : ℝ := |x.2.1| + 1
  have hmem := hB1 r hr.le c hc g hp hm hn R
  have hloc : LocallyIntegrable (chmWinR R g) volume :=
    hmem.locallyIntegrable (ENNReal.one_le_ofReal.mpr hr.le)
  obtain ⟨t, ht, hi⟩ := hloc x
  have hopen : IsOpen {z : Coord | |z.2.1| < R} :=
    isOpen_lt (by fun_prop) continuous_const
  have hx : x ∈ {z : Coord | |z.2.1| < R} := by simp [R]
  refine ⟨interior t ∩ {z : Coord | |z.2.1| < R}, inter_mem (interior_mem_nhds.2 ht)
    (hopen.mem_nhds hx), ?_⟩
  refine (hi.mono_set (inter_subset_left.trans interior_subset)).congr_fun (fun z hz => ?_)
    (isOpen_interior.inter hopen).measurableSet
  have : |z.2.1| < R := hz.2
  simp only [chmWinR, if_pos this.le]

theorem chmMollConv_of (hA : ChmMink) (hB1 : ChmWinMemLp) (hB3 : ChmWinReduce) : ChmMollConv := by
  intro r hr c hc g hp hm hn
  have hloc := chm_locInt_of hB1 r hr c hc g hp hm hn
  have hT := chm_transCont_of hB1 hB3 r hr c hc g hp hm hn
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp (ENNReal.tendsto_nhds_zero.1 hT ε hε)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  rw [Filter.eventually_atTop]
  refine ⟨N, fun n hn' => ?_⟩
  obtain ⟨hcont, hcs, hnn, hint, hsupp⟩ := chm_rho_props n
  have hsmall : 1 / ((n : ℝ) + 2) < δ := by
    have h1 : (1 / δ) < (n : ℝ) + 2 := by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn'
      linarith
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδ] at h1
    linarith
  have hA' := hA r hr.le c hc (chmRho n) g hcont hcs hint hloc
  have hρint : Integrable (chmRho n) volume := hcont.integrable_of_hasCompactSupport hcs
  have hlint : ∫⁻ y, ENNReal.ofReal |chmRho n y| = 1 := by
    have : ∫⁻ y, ENNReal.ofReal |chmRho n y| = ∫⁻ y, ENNReal.ofReal (chmRho n y) :=
      lintegral_congr fun y => by rw [abs_of_nonneg (hnn y)]
    rw [this, ← ofReal_integral_eq_lintegral_ofReal hρint (Eventually.of_forall hnn), hint]
    simp
  by_cases hεt : ε = ⊤
  · simp [hεt]
  refine hA'.trans ?_
  calc ∫⁻ y, ENNReal.ofReal |chmRho n y| * cylNorm c r (fun x => g (x - y) - g x)
      ≤ ∫⁻ y, ENNReal.ofReal |chmRho n y| * ε := by
        refine lintegral_mono fun y => ?_
        by_cases h0 : chmRho n y = 0
        · simp [h0]
        · refine mul_le_mul_right ?_ _
          have hy : ‖y‖ ≤ 1 / ((n : ℝ) + 2) := by
            by_contra hcon
            exact h0 (hsupp y (not_le.mp hcon))
          exact hδ' (by rw [dist_zero_right]; exact lt_of_le_of_lt hy hsmall)
    _ = ε := by rw [lintegral_mul_const' _ _ hεt, hlint, one_mul]

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.chmMollConv_of
