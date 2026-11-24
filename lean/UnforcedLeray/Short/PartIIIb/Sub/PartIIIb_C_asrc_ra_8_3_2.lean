import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5

/-!
# `PartIII-b:C/asrc/ra/8/3/2` : `HpAL2` from three leaves and `HpAC2`

Source: `the November 2 reference manuscript`
4963-4977 (the Gaussian sums `h^p_A = Σ_j [V_j, A^y_mer x_j]`), 4978 ("the sums and their required
derivatives converge by Gaussian decay"), 5029-5032.

Reduction.  (i) `hpAMag ≤ K |A^y(s)| · gEnv(x)` pointwise, with the Gaussian lattice envelope
`gEnv`; (ii) `|A^y(s)| ≤ M(A) s^{5/2}`; (iii) the cell `L²` norm of `gEnv` is bounded;
(iv) measurability from `HpAC2` (`hpA` is `C²` in `(s,x)`, so `hpAMag` is continuous in `x`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (Params)

/-- The Gaussian lattice envelope `Σ_j (1+|x_j|)^4 e^{-|x_j|²/9}`, `x_j = (q - jc, η)`
(`e^{-|y|²/(4a)} ≤ e^{-|y|²/9}` as `a = 1 + νs ≤ 2.1`). -/
def gEnv (ν : ℝ) (x : ℝ × ℝ) : ℝ :=
  ∑' j : ℤ, (1 + ‖xj ν j x‖) ^ 4 * Real.exp (-(‖xj ν j x‖ ^ 2) / 9)

/-- **Leaf (i): pointwise Gaussian-sum bound** (source 4963-4977, 4978): for `0 < ν`,
`0 < s ≤ 1.1/ν`, `‖h^p_A‖ + ‖Dh^p_A‖ ≤ K |A^y(s)|_F gEnv(x)`, `K` absolute.  Needs
`D h^p_A = Σ_j D(term_j)` (Gaussian decay, locally uniform) and the bounds of `V_j, DV_j, D²V_j`
(`gp_fderiv_Vj_norm`, `hessVjBound`) with `a = 1 + νs ∈ [1, 2.1]`. -/
def HpAPointwise : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (ν : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ),
    0 < ν → 0 < s → s ≤ (11 / 10) / ν →
      hpAMag ν χf A s x ≤ K * frob (Ay ν χf A s) * gEnv ν x

/-- **Leaf (iii): cell `L²` bound of the envelope** (source 4963-4977): in the normalized cell
measure `dq/c dη`, `c = ν⁻²`, `∫ gEnv² ≤ (C ν^{-k})²` for `0 < ν ≤ 1` (the `j = 0` Gaussian
integrates to a constant, the other centers are `≥ c/2 ≥ 1/2` away and sum geometrically). -/
def GEnvL2 : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ ν : ℝ, 0 < ν → ν ≤ 1 →
    ∫⁻ x, ENNReal.ofReal (gEnv ν x ^ 2) ∂(UnforcedLeray.Cyl.avgμ ((ν ^ 2)⁻¹))
      ≤ ENNReal.ofReal ((C * ν⁻¹ ^ k) ^ 2)

/-- **Leaf (ii): `M(A)` is a finite supremum** (source 4955-4962): the set defining `M(A)` is
bounded above (from `IsAffElem.bdd`, `A^y = χ_f A` with `χ_f(s) = χ̂_f(νs)` having bounded
`(s∂_s)^i` derivatives, Leibniz). -/
def AffMBdd (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν : ℝ), 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A →
    BddAbove ((fun s => s ^ (-(5 / 2 : ℝ)) * affSum 6 (Ay ν χf A) s) '' Ioc 0 ((11 / 10) / ν))

theorem gEnv_nonneg (ν : ℝ) (x : ℝ × ℝ) : 0 ≤ gEnv ν x :=
  tsum_nonneg fun _ => by positivity

theorem frob_le_affM (χf : ℝ → ℝ) (ν : ℝ) (A : ℝ → Mat3)
    (hb : BddAbove ((fun s => s ^ (-(5 / 2 : ℝ)) * affSum 6 (Ay ν χf A) s) '' Ioc 0 ((11 / 10) / ν)))
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ (11 / 10) / ν) :
    frob (Ay ν χf A s) ≤ affM ν χf A * s ^ (5 / 2 : ℝ) := by
  have h0 : frob (Ay ν χf A s) ≤ affSum 6 (Ay ν χf A) s := by
    unfold affSum
    have := Finset.single_le_sum (f := fun j => frob (sDerivIter j (Ay ν χf A) s))
      (fun j _ => by unfold frob; exact Real.sqrt_nonneg _) (Finset.mem_range.2 (by norm_num : 0 < 6 + 1))
    simpa [sDerivIter] using this
  have h1 : s ^ (-(5 / 2 : ℝ)) * affSum 6 (Ay ν χf A) s ≤ affM ν χf A :=
    le_csSup hb ⟨s, ⟨hs, hs1⟩, rfl⟩
  have h2 : 0 < s ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hs _
  have h3 : s ^ (-(5 / 2 : ℝ)) * s ^ (5 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hs]; norm_num
  calc frob (Ay ν χf A s) ≤ affSum 6 (Ay ν χf A) s := h0
    _ = (s ^ (-(5 / 2 : ℝ)) * affSum 6 (Ay ν χf A) s) * s ^ (5 / 2 : ℝ) := by
        rw [mul_right_comm, h3]; ring
    _ ≤ affM ν χf A * s ^ (5 / 2 : ℝ) := mul_le_mul_of_nonneg_right h1 h2.le

/-- `hpA` is `C²` in `x` for `s > 0` once it is `C²` in `(s,x)`. -/
theorem hpA_contDiff_slice (as : ℝ) (χf : ℝ → ℝ) (h : HpAC2 as χf) (hχ : IsSourceCutoffC χf)
    {ν : ℝ} (hν : 0 < ν) {A : ℝ → Mat3} (hA : IsAffElem as A) {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ 2 (hpA ν χf A s) := by
  have h1 := h hχ ν hν A hA
  have hc : ContDiff ℝ 2 (fun x : ℝ × ℝ => ((s, x) : ℝ × (ℝ × ℝ))) :=
    contDiff_const.prodMk contDiff_id
  have := h1.comp hc.contDiffOn (s := univ) (fun x _ => by simp [hs])
  simpa [contDiffOn_univ, Function.comp_def] using this

/-- `x ↦ ‖hpA‖ + ‖Dhpa‖` is continuous in `x` for `s > 0` once `hpA` is `C²` in `(s,x)`. -/
theorem hpAMag_continuous (as : ℝ) (χf : ℝ → ℝ) (h : HpAC2 as χf) (hχ : IsSourceCutoffC χf)
    {ν : ℝ} (hν : 0 < ν) {A : ℝ → Mat3} (hA : IsAffElem as A) {s : ℝ} (hs : 0 < s) :
    Continuous (hpAMag ν χf A s) := by
  have hsl := hpA_contDiff_slice as χf h hχ hν hA hs
  have hf : Continuous (fderiv ℝ (hpA ν χf A s)) := hsl.continuous_fderiv (by norm_num)
  unfold hpAMag
  exact hsl.continuous.norm.add hf.norm

theorem hpAL2_of (as : ℝ) (χf : ℝ → ℝ) (h1 : HpAC2 as χf) (h2 : HpAPointwise) (h3 : GEnvL2)
    (h4 : AffMBdd as χf) : HpAL2 as χf := by
  intro hχ dm dp hdm
  obtain ⟨K, hK0, hK⟩ := h2
  obtain ⟨C, k, hC⟩ := h3
  refine ⟨K * C, k, 1, one_pos, ?_⟩
  intro p d hreg hν1 A hA s hs hs1
  have hν : 0 < p.ν := p.ν_pos
  have hcont := hpAMag_continuous as χf h1 hχ hν hA hs
  refine ⟨?_, ?_⟩
  · exact (ENNReal.continuous_ofReal.comp (hcont.pow 2)).measurable.aemeasurable
  · have hc : p.c = (p.ν ^ 2)⁻¹ := hreg.c_eq
    rw [hc]
    set B : ℝ := K * (affM p.ν χf A * s ^ (5 / 2 : ℝ)) with hB
    have hfr := frob_le_affM χf p.ν A (h4 hχ p.ν hν A hA) hs hs1
    have hpt : ∀ x : ℝ × ℝ, ENNReal.ofReal (hpAMag p.ν χf A s x ^ 2) ≤
        ENNReal.ofReal (B ^ 2) * ENNReal.ofReal (gEnv p.ν x ^ 2) := by
      intro x
      have hg := gEnv_nonneg p.ν x
      have hm : 0 ≤ hpAMag p.ν χf A s x := by unfold hpAMag; positivity
      have e1 := hK p.ν χf A s x hν hs hs1
      have e2 : K * frob (Ay p.ν χf A s) * gEnv p.ν x ≤ B * gEnv p.ν x := by
        rw [hB]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfr hK0) hg
      have e3 := e1.trans e2
      rw [← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      calc hpAMag p.ν χf A s x ^ 2 ≤ (B * gEnv p.ν x) ^ 2 := pow_le_pow_left₀ hm e3 2
        _ = B ^ 2 * gEnv p.ν x ^ 2 := by ring
    calc ∫⁻ x, ENNReal.ofReal (hpAMag p.ν χf A s x ^ 2) ∂(UnforcedLeray.Cyl.avgμ ((p.ν ^ 2)⁻¹))
        ≤ ∫⁻ x, ENNReal.ofReal (B ^ 2) * ENNReal.ofReal (gEnv p.ν x ^ 2)
            ∂(UnforcedLeray.Cyl.avgμ ((p.ν ^ 2)⁻¹)) := lintegral_mono hpt
      _ = ENNReal.ofReal (B ^ 2) * ∫⁻ x, ENNReal.ofReal (gEnv p.ν x ^ 2)
            ∂(UnforcedLeray.Cyl.avgμ ((p.ν ^ 2)⁻¹)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (B ^ 2) * ENNReal.ofReal ((C * p.ν⁻¹ ^ k) ^ 2) :=
          by gcongr; exact hC p.ν hν hν1
      _ = ENNReal.ofReal ((K * C * p.ν⁻¹ ^ k * affM p.ν χf A * s ^ (5 / 2 : ℝ)) ^ 2) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [hB]; ring

end UnforcedLeray.Short.PartIIIb.Concrete
