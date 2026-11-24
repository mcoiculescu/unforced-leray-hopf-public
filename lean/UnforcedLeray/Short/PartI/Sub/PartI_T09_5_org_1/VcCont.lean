import UnforcedLeray.Short.PartI.Sub.PartI_T09_5_org_1.FiniteEnergy
import UnforcedLeray.Short.Spine.Proofs.EstVcRegularity
import UnforcedLeray.Units.B0151.Linf
import UnforcedLeray.Units.B0147
import UnforcedLeray.Units.B0147.Lattice
import UnforcedLeray.Lib.Train.VortexBounds
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# `PartI:T09/5/org/1/org/a`: `V_c^p` is `H^k(cell)`-continuous at age `0`

Source: `the November 2 reference manuscript`, lines 294 and 341-344
(`V_c^p = ∑ₙ ∇^⊥ψ^p(q - nc, η, s)`, `ψ^p = -2a⁻¹ e^{-|x|²/(4a)}`, `a = 1 + νs`).

This file proves `VcCellL2Cont` from three analytic inputs, each stated as a `def` below:

* `VcAgePointwise`: for each `z`, the word derivatives of `V_c(s)` at `z` converge as `s → 0⁺`;
* `VcAgeMeasurable`: the word derivatives of `V_c(s)`, `s ≥ 0`, are measurable;
* `VcAgeDominated`: a `s`-uniform integrable envelope for the squared differences on the cell
  (eventually as `s → 0⁺`).

The assembly (dominated convergence for `lintegral` along `𝓝[≥] 0`) is proved here.  The three

-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec Vc)

/-- Pointwise age-continuity of the word derivatives of `V_c` at `s = 0` (from the right). -/
def VcAgePointwise : Prop :=
  ∀ (ν c : ℝ), 0 < ν → 1 ≤ c → ∀ (w : List Bool) (k : Fin 2) (z : Plane),
    Tendsto (fun s : ℝ => wordComp w (Vc ν c s) k z) (nhdsWithin (0 : ℝ) (Ici 0))
      (𝓝 (wordComp w (Vc ν c 0) k z))

/-- Measurability of the word derivatives of `V_c(s)` for `s ≥ 0`. -/
def VcAgeMeasurable : Prop :=
  ∀ (ν c : ℝ), 0 < ν → 1 ≤ c → ∀ (w : List Bool) (k : Fin 2) (s : ℝ), 0 ≤ s →
    Measurable (wordComp w (Vc ν c s) k)

/-- An integrable envelope for the squared age differences on one cell, eventually as `s → 0⁺`. -/
def VcAgeDominated : Prop :=
  ∀ (ν c : ℝ), 0 < ν → 1 ≤ c → ∀ (w : List Bool) (k : Fin 2), ∃ G : Plane → ℝ,
    Integrable G (Cyl.cellμ c) ∧ ∀ᶠ s in nhdsWithin (0 : ℝ) (Ici 0), ∀ z ∈ Cyl.cell c,
      (wordComp w (Vc ν c s) k z - wordComp w (Vc ν c 0) k z) ^ 2 ≤ G z

/-- **Assembly.** From the three analytic inputs, `V_c^p` is `H^k(cell)`-continuous at age `0`. -/
theorem vcCellL2Cont_of (hP : VcAgePointwise) (hM : VcAgeMeasurable) (hD : VcAgeDominated) :
    VcCellL2Cont := by
  intro ν c hν hc w k
  obtain ⟨G, hGint, hG⟩ := hD ν c hν hc w k
  have key := tendsto_lintegral_filter_of_dominated_convergence
    (μ := Cyl.cellμ c) (l := nhdsWithin (0 : ℝ) (Ici 0))
    (F := fun s z => ENNReal.ofReal ((wordComp w (Vc ν c s) k z - wordComp w (Vc ν c 0) k z) ^ 2))
    (f := fun _ => 0) (bound := fun z => ENNReal.ofReal (G z))
    (h_bound := hG.mono fun s hs => (ae_restrict_of_forall_mem (Cyl.measurableSet_cell c) fun z hz =>
      ENNReal.ofReal_le_ofReal (hs z hz)))
    (h_fin := hGint.lintegral_lt_top.ne)
    (h_lim := ae_of_all _ fun z => by
      have hdiff : Tendsto (fun s : ℝ => wordComp w (Vc ν c s) k z - wordComp w (Vc ν c 0) k z)
          (nhdsWithin (0 : ℝ) (Ici 0)) (𝓝 0) := by
        have h := (hP ν c hν hc w k z).sub (tendsto_const_nhds (x := wordComp w (Vc ν c 0) k z))
        simpa using h
      have hsq : Tendsto (fun s : ℝ => (wordComp w (Vc ν c s) k z - wordComp w (Vc ν c 0) k z) ^ 2)
          (nhdsWithin (0 : ℝ) (Ici 0)) (𝓝 0) := by
        simpa using hdiff.pow 2
      have h2 : Tendsto (fun s : ℝ => ENNReal.ofReal ((wordComp w (Vc ν c s) k z -
          wordComp w (Vc ν c 0) k z) ^ 2)) (nhdsWithin (0 : ℝ) (Ici 0))
          (𝓝 (ENNReal.ofReal 0)) :=
        (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hsq
      rw [ENNReal.ofReal_zero] at h2
      exact h2)
    (hF_meas := by
      refine eventually_nhdsWithin_of_forall fun s hs => ?_
      have hm := (hM ν c hν hc w k s hs).sub (hM ν c hν hc w k 0 le_rfl)
      exact (hm.pow_const 2).ennreal_ofReal)
  have hzero : (∫⁻ _ : Plane, (0 : ℝ≥0∞) ∂(Cyl.cellμ c)) = 0 := by simp
  rw [hzero] at key
  exact key

/-- The measurability input is discharged: `V_c(s)` is `C^∞` for `s ≥ 0` (Spine), and word
derivatives of smooth functions are smooth (`B0151.contDiff_derivWord`). -/
theorem vcAgeMeasurable_proof : VcAgeMeasurable := by
  intro ν c hν hc w k s hs
  have hw : 0 < UnforcedLeray.Train.width ν s := Spine.vcReg_width_pos hν hs
  have hV : ContDiff ℝ ∞ (Vc ν c s) := Spine.vcReg_contDiff_Vc (by linarith) hw
  have h1 : ContDiff ℝ ∞ (fun x => Vc ν c s x k) :=
    (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hV
  exact ((B0151.contDiff_derivWord h1 w).continuous).measurable


/-! ### The analytic inputs, from the rescaled lattice representation (B0147) -/

section Analytic

open UnforcedLeray.B0147 (lam lam_pos lam_sq GP_U derivWord_velocity)
open UnforcedLeray.B0146 (latticeSum shift)

/-- Rescaled lattice representation of `∂_w V_c^k` with a fixed Gaussian-bounded profile `g`. -/
theorem vcRep (w : List Bool) (k : Fin 2) :
    ∃ (g : Plane → ℝ) (K β : ℝ), Continuous g ∧ 0 ≤ K ∧ 0 < β ∧
      (∀ y : Plane, |g y| ≤ K * Real.exp (-(β * (y.1 ^ 2 + y.2 ^ 2)))) ∧
      ∀ ν c s : ℝ, c ≠ 0 → 0 < UnforcedLeray.Train.width ν s →
        wordComp w (Vc ν c s) k = fun z =>
          lam (UnforcedLeray.Train.width ν s) ^ 3 * lam (UnforcedLeray.Train.width ν s) ^ w.length *
            ∑' n : ℤ, g (lam (UnforcedLeray.Train.width ν s) * z.1 -
              n * (lam (UnforcedLeray.Train.width ν s) * c),
              lam (UnforcedLeray.Train.width ν s) * z.2) := by
  obtain ⟨g, hg, hw⟩ := (GP_U k).derivWord_lattice w
  obtain ⟨K, β, hK, hβ, hb⟩ := hg.bound
  refine ⟨g, K, β, hg.continuous, hK, hβ, fun y => ?_, fun ν c s hc ha => ?_⟩
  · have := hb y
    simpa [UnforcedLeray.GaussianVortex.radiusSq] using this
  · unfold wordComp
    rw [UnforcedLeray.Train.Vc_comp_eq]
    exact derivWord_velocity hc ha k w hw

/-- Age parameters in `[0, 1/ν]`: `μ = lam (width)` has `μ² ∈ [1/2, 1]`. -/
theorem mu_facts {ν s : ℝ} (hν : 0 < ν) (hs : s ∈ Icc (0 : ℝ) (1 / ν)) :
    0 < UnforcedLeray.Train.width ν s ∧
      0 < lam (UnforcedLeray.Train.width ν s) ∧ lam (UnforcedLeray.Train.width ν s) ≤ 1 ∧
      1 / 2 ≤ lam (UnforcedLeray.Train.width ν s) ^ 2 := by
  obtain ⟨h0, h1⟩ := hs
  have hws : ν * s ≤ 1 := by
    have := mul_le_mul_of_nonneg_left h1 hν.le
    rwa [mul_one_div_cancel hν.ne'] at this
  have hw0 : 0 < UnforcedLeray.Train.width ν s := by
    unfold UnforcedLeray.Train.width; nlinarith [mul_nonneg hν.le h0]
  have hw1 : 1 ≤ UnforcedLeray.Train.width ν s := by
    unfold UnforcedLeray.Train.width; nlinarith [mul_nonneg hν.le h0]
  have hw2 : UnforcedLeray.Train.width ν s ≤ 2 := by
    unfold UnforcedLeray.Train.width; linarith
  have hsq := lam_sq hw0
  have hpos := lam_pos hw0
  refine ⟨hw0, hpos, ?_, ?_⟩
  · by_contra h
    push Not at h
    have : 1 < lam (UnforcedLeray.Train.width ν s) ^ 2 := by nlinarith
    rw [hsq] at this
    have := inv_le_one_of_one_le₀ hw1
    linarith
  · rw [hsq]
    rw [le_inv_comm₀ (by norm_num) hw0]
    simpa using hw2

theorem lam_width_zero (ν : ℝ) : lam (UnforcedLeray.Train.width ν 0) = 1 := by
  simp [lam, UnforcedLeray.Train.width]

theorem continuousAt_mu {ν s : ℝ} (hw : 0 < UnforcedLeray.Train.width ν s) :
    ContinuousAt (fun t : ℝ => lam (UnforcedLeray.Train.width ν t)) s := by
  unfold lam UnforcedLeray.Train.width at *
  have h1 : ContinuousAt (fun t : ℝ => Real.sqrt (1 + ν * t)) s :=
    (Real.continuous_sqrt.continuousAt).comp (by fun_prop)
  exact h1.inv₀ (Real.sqrt_pos.2 hw).ne'

/-- **Pointwise age continuity.** -/
theorem vcAgePointwise_proof : VcAgePointwise := by
  intro ν c hν hc w k z
  have hc0 : c ≠ 0 := by positivity
  obtain ⟨g, K, β, hgc, hK, hβ, hgb, hrep⟩ := vcRep w k
  set μ : ℝ → ℝ := fun t => lam (UnforcedLeray.Train.width ν t) with hμ
  have hw0 : 0 < UnforcedLeray.Train.width ν 0 := by simp [UnforcedLeray.Train.width]
  have hμc : ContinuousAt μ 0 := continuousAt_mu hw0
  have hμ0 : μ 0 = 1 := lam_width_zero ν
  have hev : ∀ᶠ s in nhdsWithin (0 : ℝ) (Ici 0), s ∈ Icc (0 : ℝ) (1 / ν) :=
    Icc_mem_nhdsGE (by positivity)
  have hF : ∀ s, 0 ≤ s → wordComp w (Vc ν c s) k z = μ s ^ 3 * μ s ^ w.length *
      ∑' n : ℤ, g (μ s * z.1 - n * (μ s * c), μ s * z.2) := by
    intro s hs
    have := hrep ν c s hc0 (by unfold UnforcedLeray.Train.width; nlinarith [mul_nonneg hν.le hs])
    exact congrFun this z
  have hF0 := hF 0 le_rfl
  have hsum : Tendsto (fun s : ℝ => ∑' n : ℤ, g (μ s * z.1 - n * (μ s * c), μ s * z.2))
      (nhdsWithin (0 : ℝ) (Ici 0)) (𝓝 (∑' n : ℤ, g (μ 0 * z.1 - n * (μ 0 * c), μ 0 * z.2))) := by
    refine tendsto_tsum_of_dominated_convergence
      (bound := fun n : ℤ => K * Real.exp (-((β / 2) * (z.1 - n * c) ^ 2)))
      ((B0146.summable_exp_shift (by positivity : 0 < β / 2) hc0 z.1).mul_left K) (fun n => ?_) ?_
    · have hco : ContinuousAt (fun s => (μ s * z.1 - n * (μ s * c), μ s * z.2)) 0 := by
        exact (((hμc.mul continuousAt_const).sub (continuousAt_const.mul
          (hμc.mul continuousAt_const))).prodMk (hμc.mul continuousAt_const))
      exact ((hgc.continuousAt.comp hco).tendsto).mono_left nhdsWithin_le_nhds
    · filter_upwards [hev] with s hs n
      obtain ⟨-, hpos, -, hhalf⟩ := mu_facts hν hs
      rw [Real.norm_eq_abs]
      refine (hgb _).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hK)
      have e1 : (μ s * z.1 - n * (μ s * c)) ^ 2 = μ s ^ 2 * (z.1 - n * c) ^ 2 := by ring
      rw [e1]
      have : (1 / 2) * (z.1 - n * c) ^ 2 ≤ μ s ^ 2 * (z.1 - n * c) ^ 2 :=
        mul_le_mul_of_nonneg_right hhalf (sq_nonneg _)
      nlinarith [sq_nonneg (μ s * z.2), mul_pos hβ hβ]
  have hpow : Tendsto (fun s => μ s ^ 3 * μ s ^ w.length) (nhdsWithin (0 : ℝ) (Ici 0))
      (𝓝 (μ 0 ^ 3 * μ 0 ^ w.length)) :=
    (((hμc.tendsto.pow 3).mul (hμc.tendsto.pow w.length))).mono_left nhdsWithin_le_nhds
  have hlim := hpow.mul hsum
  rw [hF0]
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (hF s hs).symm


/-- On the cell, `(z₁ - n c)² ≥ n²/4` for `c ≥ 1`. -/
theorem cell_shift_sq {c x : ℝ} (hc : 1 ≤ c) (hx : |x| ≤ c / 2) (n : ℤ) :
    (n : ℝ) ^ 2 / 4 ≤ (x - n * c) ^ 2 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp; positivity
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
    exact_mod_cast this
  have h1 : |(n : ℝ) * c| ≤ |x - n * c| + |x| := by
    have := abs_sub_abs_le_abs_sub ((n : ℝ) * c) x
    have h2 : |(n : ℝ) * c - x| = |x - n * c| := abs_sub_comm _ _
    linarith
  have h3 : |(n : ℝ) * c| = |(n : ℝ)| * c := by rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ c)]
  have h4 : |(n : ℝ)| / 2 ≤ |x - n * c| := by nlinarith
  have h5 : ((n : ℝ) ^ 2) / 4 = (|(n : ℝ)| / 2) ^ 2 := by rw [div_pow, sq_abs]; norm_num
  rw [h5, ← sq_abs (x - n * c)]
  exact pow_le_pow_left₀ (by positivity) h4 2

theorem vcAgeDominated_proof : VcAgeDominated := by
  intro ν c hν hc w k
  have hc0 : c ≠ 0 := by positivity
  obtain ⟨g, K, β, hgc, hK, hβ, hgb, hrep⟩ := vcRep w k
  set T : ℝ := ∑' n : ℤ, Real.exp (-((β / 8) * (n : ℝ) ^ 2)) with hT
  have hT0 : 0 ≤ T := tsum_nonneg fun _ => (Real.exp_pos _).le
  have hTs : Summable (fun n : ℤ => Real.exp (-((β / 8) * (n : ℝ) ^ 2))) := by
    have := B0147.summable_theta (γ := β / 8) (by positivity)
    exact this
  set C : ℝ := K * T with hC
  have hC0 : 0 ≤ C := mul_nonneg hK hT0
  -- pointwise bound on the cell, for s in [0, 1/ν]
  have hbound : ∀ s ∈ Icc (0 : ℝ) (1 / ν), ∀ z ∈ Cyl.cell c,
      |wordComp w (Vc ν c s) k z| ≤ C * Real.exp (-((β / 2) * z.2 ^ 2)) := by
    intro s hs z hz
    obtain ⟨hw0, hpos, hle1, hhalf⟩ := mu_facts hν hs
    have hx : |z.1| ≤ c / 2 := by
      have hz1 : z.1 ∈ Ico (-c / 2) (c / 2) := hz.1
      rw [abs_le]; constructor <;> linarith [hz1.1, hz1.2]
    rw [hrep ν c s hc0 hw0]
    set μ := lam (UnforcedLeray.Train.width ν s) with hμ
    have hμpow : μ ^ 3 * μ ^ w.length ≤ 1 :=
      mul_le_one₀ (pow_le_one₀ hpos.le hle1) (by positivity) (pow_le_one₀ hpos.le hle1)
    have hterm : ∀ n : ℤ, ‖g (μ * z.1 - n * (μ * c), μ * z.2)‖ ≤
        K * Real.exp (-((β / 2) * z.2 ^ 2)) * Real.exp (-((β / 8) * (n : ℝ) ^ 2)) := by
      intro n
      rw [Real.norm_eq_abs]
      refine (hgb _).trans ?_
      rw [mul_assoc, ← Real.exp_add]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hK
      have e1 : (μ * z.1 - n * (μ * c)) ^ 2 = μ ^ 2 * (z.1 - n * c) ^ 2 := by ring
      have e2 : (μ * z.2) ^ 2 = μ ^ 2 * z.2 ^ 2 := by ring
      have h3 := cell_shift_sq hc hx n
      have h4 : (1 / 2) * (z.1 - n * c) ^ 2 ≤ μ ^ 2 * (z.1 - n * c) ^ 2 :=
        mul_le_mul_of_nonneg_right hhalf (sq_nonneg _)
      have h5 : (1 / 2) * z.2 ^ 2 ≤ μ ^ 2 * z.2 ^ 2 :=
        mul_le_mul_of_nonneg_right hhalf (sq_nonneg _)
      rw [e1, e2]
      nlinarith [mul_le_mul_of_nonneg_left h3 hβ.le, mul_le_mul_of_nonneg_left h4 hβ.le,
        mul_le_mul_of_nonneg_left h5 hβ.le]
    have hsumm : Summable (fun n : ℤ => K * Real.exp (-((β / 2) * z.2 ^ 2)) *
        Real.exp (-((β / 8) * (n : ℝ) ^ 2))) := hTs.mul_left _
    have hnorm : ‖∑' n : ℤ, g (μ * z.1 - n * (μ * c), μ * z.2)‖ ≤
        K * Real.exp (-((β / 2) * z.2 ^ 2)) * T := by
      have hsg : Summable (fun n : ℤ => g (μ * z.1 - n * (μ * c), μ * z.2)) :=
        Summable.of_norm_bounded hsumm hterm
      refine (norm_tsum_le_tsum_norm hsg.norm).trans ?_
      refine (hsg.norm.tsum_le_tsum hterm hsumm).trans ?_
      rw [tsum_mul_left]
    have hexp := Real.exp_pos (-((β / 2) * z.2 ^ 2))
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ μ ^ 3 * μ ^ w.length)]
    calc μ ^ 3 * μ ^ w.length * |∑' n : ℤ, g (μ * z.1 - n * (μ * c), μ * z.2)|
        ≤ 1 * (K * Real.exp (-((β / 2) * z.2 ^ 2)) * T) :=
          mul_le_mul hμpow (by simpa [Real.norm_eq_abs] using hnorm) (abs_nonneg _) zero_le_one
      _ = C * Real.exp (-((β / 2) * z.2 ^ 2)) := by rw [hC]; ring
  refine ⟨fun z => 4 * C ^ 2 * Real.exp (-(β * z.2 ^ 2)), ?_, ?_⟩
  · -- integrability on the cell
    have hint : Integrable (fun z : Plane => (4 * C ^ 2) * Real.exp (-(β * z.2 ^ 2)))
        (Cyl.cellμ c) := by
      unfold Cyl.cellμ Cyl.cell
      have h1 : Integrable (fun _ : ℝ => (4 * C ^ 2)) (volume.restrict (Ico (-c / 2) (c / 2))) :=
        integrableOn_const (by simp)
      have h2 : Integrable (fun y : ℝ => Real.exp (-(β * y ^ 2))) volume :=
        by simpa [neg_mul] using integrable_exp_neg_mul_sq hβ
      have h3 := h1.mul_prod h2
      have e : (volume : Measure Plane).restrict (Ico (-c / 2) (c / 2) ×ˢ (univ : Set ℝ)) =
          (volume.restrict (Ico (-c / 2) (c / 2))).prod volume := by
        have := Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
          (Ico (-c / 2) (c / 2)) (univ : Set ℝ)
        rw [Measure.restrict_univ] at this
        rw [Measure.volume_eq_prod]
        exact this.symm
      rw [e]
      exact h3
    exact hint
  · filter_upwards [Icc_mem_nhdsGE (by positivity : (0 : ℝ) < 1 / ν)] with s hs z hz
    have h1 := hbound s hs z hz
    have h0 := hbound 0 ⟨le_rfl, by positivity⟩ z hz
    set E := C * Real.exp (-((β / 2) * z.2 ^ 2))
    have hsq : (wordComp w (Vc ν c s) k z - wordComp w (Vc ν c 0) k z) ^ 2 ≤ (2 * E) ^ 2 := by
      have : |wordComp w (Vc ν c s) k z - wordComp w (Vc ν c 0) k z| ≤ 2 * E := by
        calc _ ≤ |wordComp w (Vc ν c s) k z| + |wordComp w (Vc ν c 0) k z| := abs_sub _ _
          _ ≤ 2 * E := by linarith
      calc _ = |wordComp w (Vc ν c s) k z - wordComp w (Vc ν c 0) k z| ^ 2 := (sq_abs _).symm
        _ ≤ (2 * E) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
    refine hsq.trans (le_of_eq ?_)
    have : Real.exp (-((β / 2) * z.2 ^ 2)) ^ 2 = Real.exp (-(β * z.2 ^ 2)) := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    simp only [E]
    rw [mul_pow, mul_pow, this]; ring

/-- **Target.** `V_c^p` is `H^k(cell)`-continuous at age `0`. -/
theorem vcCellL2Cont_proof : VcCellL2Cont :=
  vcCellL2Cont_of vcAgePointwise_proof vcAgeMeasurable_proof vcAgeDominated_proof

end Analytic

end UnforcedLeray.Short.PartI
