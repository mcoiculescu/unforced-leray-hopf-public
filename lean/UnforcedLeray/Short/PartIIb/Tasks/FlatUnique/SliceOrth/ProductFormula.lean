import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_5
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.DualConstancy.TestZero.Eq.Integrable

/-!
# Helper for `PartII-b:T11/5/4` (`SliceProductFormula`): the product formula

Source: `the November 2 reference manuscript` lines 1923-1938 and `Sub/T11.lean`
step 4. `ageμ c 0 = (dσ|_{σ>0}) ⊗ avgμ c` (density `s^0 = 1`), so Fubini (`integral_prod`) applies
once the integrand is integrable.  Integrability of `streamPair b θ ζ` is the box lemma
`integrable_pair_of_box` (from `TestZero/Eq/Integrable.lean`): `θ` is supported in a compact
subset `[σ₀, H]` of `(0, ∞)`, and `∇^⊥ζ` vanishes for `|η| > L`, so the integrand vanishes outside a
box on which the `H_r` norm dominates `L^1` of the cell measure.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- `ageμ c 0 = (vol|_{(0,∞)}) ⊗ avgμ c`: the density `s ↦ ofReal (s^0)` is `1`. -/
theorem pf_ageμ_zero_eq_prod (c : ℝ) :
    Axi.ageμ c 0 = (volume.restrict (Ioi (0 : ℝ))).prod (Cyl.avgμ c) := by
  have h1 : (fun s : ℝ => ENNReal.ofReal (s ^ (0 : ℝ))) = 1 := by
    funext s
    simp
  rw [Axi.ageμ, h1, withDensity_one]

/-- `∇ζ = 0` at points where `ζ` vanishes on the open set `{L < |η|}`. -/
theorem pf_fderiv_eq_zero (ζ : ℝ × ℝ → ℝ) (L : ℝ)
    (hL : ∀ p : ℝ × ℝ, L ≤ |p.2| → ζ p = 0) (p : ℝ × ℝ) (hp : L < |p.2|) :
    fderiv ℝ ζ p = 0 := by
  have hU : IsOpen {q : ℝ × ℝ | L < |q.2|} :=
    isOpen_lt continuous_const (continuous_abs.comp continuous_snd)
  have hev : ζ =ᶠ[𝓝 p] (fun _ => (0 : ℝ)) :=
    Filter.eventually_of_mem (hU.mem_nhds (show p ∈ {q : ℝ × ℝ | L < |q.2|} from hp))
      (fun q hq => hL q (le_of_lt (show L < |q.2| from hq)))
  rw [hev.fderiv_eq]
  simp

/-- `∇^⊥ζ` vanishes for `L < |η|`. -/
theorem pf_perpGrad_eq_zero (ζ : ℝ × ℝ → ℝ) (L : ℝ)
    (hL : ∀ p : ℝ × ℝ, L ≤ |p.2| → ζ p = 0) (p : ℝ × ℝ) (hp : L < |p.2|) (i : Fin 2) :
    perpGrad ζ p i = 0 := by
  fin_cases i <;> simp [perpGrad, pf_fderiv_eq_zero ζ L hL p hp]

/-- Continuity of the components of `∇^⊥ζ` for a smooth `ζ`. -/
theorem pf_perpGrad_continuous (ζ : ℝ × ℝ → ℝ) (hζ : ContDiff ℝ ∞ ζ) (i : Fin 2) :
    Continuous fun p : ℝ × ℝ => perpGrad ζ p i := by
  have hc : Continuous (fderiv ℝ ζ) := hζ.continuous_fderiv (by simp)
  have h01 : Continuous fun p : ℝ × ℝ => fderiv ℝ ζ p (0, 1) :=
    hc.clm_apply continuous_const
  have h10 : Continuous fun p : ℝ × ℝ => fderiv ℝ ζ p (1, 0) :=
    hc.clm_apply continuous_const
  fin_cases i
  · show Continuous fun p : ℝ × ℝ => fderiv ℝ ζ p (0, 1)
    exact h01
  · show Continuous fun p : ℝ × ℝ => -fderiv ℝ ζ p (1, 0)
    exact h10.neg

/-- Integrability of the product pairing `streamPair b θ ζ` for `ageμ c 0`. -/
theorem pf_integrable {c r : ℝ} (hc : 0 < c) (hr : 1 < r) {b : CProf} (hb : InHr c r b)
    (θ : ℝ → ℝ) (ζ : ℝ × ℝ → ℝ) (hθ : TimeTest θ) (hζ : NiceStream c ζ) :
    Integrable (streamPair b θ ζ) (Axi.ageμ c 0) := by
  -- a lower bound `σ₀ > 0` for the support of `θ`
  obtain ⟨σ₀, hσ₀, hσ₀K⟩ : ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∀ t ∈ tsupport θ, σ₀ ≤ t := by
    have hK : IsCompact (tsupport θ) := hθ.compact
    have hcont : ContinuousOn (fun t : ℝ => t⁻¹) (tsupport θ) :=
      continuousOn_id.inv₀ fun t ht => (show (0 : ℝ) < t from hθ.supp ht).ne'
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
    refine ⟨1 / (|C| + 1), by positivity, fun t ht => ?_⟩
    have hpos : (0 : ℝ) < t := hθ.supp ht
    have h1 : t⁻¹ ≤ |C| := by
      have := hC t ht
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos)] at this
      exact this.trans (le_abs_self C)
    rw [div_le_iff₀ (by positivity)]
    have h2 : 1 ≤ t * |C| := by
      have := mul_le_mul_of_nonneg_left h1 hpos.le
      rwa [mul_inv_cancel₀ hpos.ne'] at this
    nlinarith [abs_nonneg C]
  -- an upper bound `H` for the support of `θ`
  obtain ⟨H, hH⟩ : ∃ H : ℝ, ∀ t ∈ tsupport θ, t ≤ H := by
    have hK : IsCompact (tsupport θ) := hθ.compact
    obtain ⟨H, hH⟩ := hK.bddAbove
    exact ⟨H, fun t ht => hH ht⟩
  -- the `η`-bound `L` for `ζ`
  obtain ⟨L, hL⟩ := hζ.compact
  have hw : ∀ i : Fin 2, Continuous fun x : Coord =>
      ((θ x.1 * perpGrad ζ x.2 i : ℝ) : ℂ) := by
    intro i
    have h1 : Continuous fun x : Coord => θ x.1 :=
      hθ.smooth.continuous.comp continuous_fst
    have h2 : Continuous fun x : Coord => perpGrad ζ x.2 i :=
      (pf_perpGrad_continuous ζ hζ.smooth i).comp continuous_snd
    exact Complex.continuous_ofReal.comp (h1.mul h2)
  have hvan : ∀ x : Coord, x ∉ dtBox σ₀ H L →
      ∀ i : Fin 2, ((θ x.1 * perpGrad ζ x.2 i : ℝ) : ℂ) = 0 := by
    intro x hx i
    by_cases h1 : x.1 ∈ Icc σ₀ H
    · have h2 : x.2.2 ∉ Icc (-L) L := fun h2 => hx ⟨h1, trivial, h2⟩
      have hLa : L < |x.2.2| := by
        by_contra hcon
        push_neg at hcon
        exact h2 (abs_le.1 hcon)
      rw [pf_perpGrad_eq_zero ζ L hL x.2 hLa i, mul_zero]
      simp
    · have hθ0 : θ x.1 = 0 :=
        image_eq_zero_of_notMem_tsupport (fun ht => h1 ⟨hσ₀K _ ht, hH _ ht⟩)
      rw [hθ0, zero_mul]
      simp
  exact integrable_pair_of_box hc hr hb σ₀ H L hσ₀
    (fun x i => ((θ x.1 * perpGrad ζ x.2 i : ℝ) : ℂ)) hw hvan

/-- **Leaf `PartII-b:T11/5/4`** (`SliceProductFormula`, product formula for `ageμ c 0`). -/
theorem sliceProductFormula : UnforcedLeray.Short.IIb.SliceProductFormula := by
  intro c r b θ ζ hc hr hb hθ hζ
  have hint := pf_integrable hc hr hb θ ζ hθ hζ
  rw [pf_ageμ_zero_eq_prod c] at hint ⊢
  exact integral_prod _ hint

end UnforcedLeray.Short.IIb
