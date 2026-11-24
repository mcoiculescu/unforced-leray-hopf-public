import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G2Org

/-!
# `PartIII-b:IIIb-D3/2/G2/FrozenReduce`: exact scaling of the frozen dual on the Gaussian sources

Source of record: `the November 2 reference manuscript`: 4352-4356 (frozen pair),
4562-4570 (Gaussian sources). Mathematics: the frozen dual of a function equal a.e. on the cell `c`
to `HProf`, `conj HProf`, `RProf` is the pairing over the cell `c/√a` of `Λ` with the periodization
of the unit-clock mode, because `J_a⁻¹` maps the cell `c` onto the cell `c/√a` and the Gaussian
sources are self-similar: `gaussE a r = a⁻² gaussE 1 (r/√a)`, `angTwo` is scale invariant.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory
open scoped ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G2

open FlatSettingInst

/-- `planeR` is homogeneous of degree one under positive scaling. -/
theorem g2fr_planeR_smul (a : ℝ) (ha : 0 ≤ a) (p q : ℝ) :
    planeR (Real.sqrt a * p, Real.sqrt a * q) = Real.sqrt a * planeR (p, q) := by
  show Real.sqrt ((Real.sqrt a * p) ^ 2 + (Real.sqrt a * q) ^ 2) =
    Real.sqrt a * Real.sqrt (p ^ 2 + q ^ 2)
  have h : (Real.sqrt a * p) ^ 2 + (Real.sqrt a * q) ^ 2 = a * (p ^ 2 + q ^ 2) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt ha]
    ring
  rw [h, Real.sqrt_mul ha]

/-- `e^{2iϑ}` is invariant under positive scaling of the point. -/
theorem g2fr_angTwo_smul (s : ℝ) (hs : 0 < s) (p q : ℝ) :
    IIIa.angTwo (s * p, s * q) = IIIa.angTwo (p, q) := by
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  unfold IIIa.angTwo
  calc ((((s * p : ℝ)) : ℂ) + ((s * q : ℝ) : ℂ) * Complex.I) ^ 2 /
        (((s * p) ^ 2 + (s * q) ^ 2 : ℝ) : ℂ)
      = ((s : ℂ) ^ 2 * (((p : ℂ) + (q : ℂ) * Complex.I) ^ 2)) /
          ((s : ℂ) ^ 2 * ((p ^ 2 + q ^ 2 : ℝ) : ℂ)) := by
        congr 1 <;> push_cast <;> ring
    _ = ((p : ℂ) + (q : ℂ) * Complex.I) ^ 2 / ((p ^ 2 + q ^ 2 : ℝ) : ℂ) :=
        mul_div_mul_left _ _ (pow_ne_zero 2 hs0)

/-- The Gaussian `E_s` in unit-clock variables: `gaussE a r = a⁻² gaussE 1 (r/√a)`. -/
theorem g2fr_gaussE_eq (a r : ℝ) (ha : 0 < a) :
    gaussE a r = (a ^ 2)⁻¹ * gaussE 1 ((Real.sqrt a)⁻¹ * r) := by
  have hsq : ((Real.sqrt a)⁻¹ * r) ^ 2 = r ^ 2 / a := by
    rw [mul_pow, inv_pow, Real.sq_sqrt ha.le, div_eq_mul_inv]
    ring
  unfold gaussE
  rw [hsq]
  ring_nf

theorem g2fr_gaussE_smul (a : ℝ) (ha : 0 < a) (R : ℝ) :
    gaussE a (Real.sqrt a * R) = (a ^ 2)⁻¹ * gaussE 1 R := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  rw [g2fr_gaussE_eq a _ ha, inv_mul_cancel_left₀ hs.ne']

/-- Derivative of the scaled Gaussian profile. -/
theorem g2fr_deriv_gaussE (a : ℝ) (ha : 0 < a) (r : ℝ) :
    deriv (gaussE a) r =
      (a ^ 2)⁻¹ * ((Real.sqrt a)⁻¹ * deriv (gaussE 1) ((Real.sqrt a)⁻¹ * r)) := by
  have hf : gaussE a = fun x => (a ^ 2)⁻¹ * gaussE 1 ((Real.sqrt a)⁻¹ * x) :=
    funext fun x => g2fr_gaussE_eq a x ha
  rw [hf, deriv_const_mul_field']
  dsimp only
  rw [deriv_comp_mul_left, smul_eq_mul]

theorem g2fr_gaussRdE_smul (a : ℝ) (ha : 0 < a) (R : ℝ) :
    gaussRdE a (Real.sqrt a * R) = (a ^ 2)⁻¹ * gaussRdE 1 R := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hsi : Real.sqrt a * (Real.sqrt a)⁻¹ = 1 := mul_inv_cancel₀ hs.ne'
  unfold gaussRdE
  rw [g2fr_deriv_gaussE a ha, inv_mul_cancel_left₀ hs.ne']
  linear_combination ((a ^ 2)⁻¹ * R * deriv (gaussE 1) R) * hsi

/-- The angular-two mode scales as `a⁻²` (exact self-similarity). -/
theorem g2fr_hMode_smul (a : ℝ) (ha : 0 < a) (p q : ℝ) :
    hMode a (Real.sqrt a * p, Real.sqrt a * q) = ((a ^ 2 : ℝ) : ℂ)⁻¹ * hMode 1 (p, q) := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  unfold hMode
  rw [g2fr_planeR_smul a ha.le, g2fr_angTwo_smul _ hs, g2fr_gaussRdE_smul a ha]
  push_cast
  ring

/-- The radial mode scales as `a⁻²` (exact self-similarity). -/
theorem g2fr_rMode_smul (a : ℝ) (ha : 0 < a) (p q : ℝ) :
    rMode a (Real.sqrt a * p, Real.sqrt a * q) = ((a ^ 2 : ℝ) : ℂ)⁻¹ * rMode 1 (p, q) := by
  unfold rMode
  rw [g2fr_planeR_smul a ha.le, g2fr_gaussRdE_smul a ha, g2fr_gaussE_smul a ha]
  push_cast
  ring

/-- Conjugate of the angular-two mode scales in the same way. -/
theorem g2fr_conj_hG (a : ℝ) (ha : 0 < a) (p q : ℝ) :
    (fun u => conj (hMode a u)) (Real.sqrt a * p, Real.sqrt a * q)
      = ((a ^ 2 : ℝ) : ℂ)⁻¹ * (fun u => conj (hMode 1 u)) (p, q) := by
  dsimp only
  rw [g2fr_hMode_smul a ha, map_mul, map_inv₀, Complex.conj_ofReal]

/-- Scaling of a periodization: `J_a⁻¹ P_c G = P_{c/√a} H` when `G(√a ·) = a⁻² H`. -/
theorem g2fr_jscale_periodize (a c : ℝ) (ha : 0 < a) (G H : ℝ × ℝ → ℂ)
    (hG : ∀ p q : ℝ, G (Real.sqrt a * p, Real.sqrt a * q) = ((a ^ 2 : ℝ) : ℂ)⁻¹ * H (p, q))
    (y : ℝ × ℝ) :
    IIIa.JscaleInv a (IIIa.periodizeC c G) y = IIIa.periodizeC (c / Real.sqrt a) H y := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hs0 : Real.sqrt a ≠ 0 := hs.ne'
  have hne : ((a ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos ha 2).ne'
  have key : Real.sqrt a * (c / Real.sqrt a) = c := by field_simp
  unfold IIIa.JscaleInv IIIa.periodizeC
  dsimp only
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  have hpt : (Real.sqrt a * y.1 - (n : ℝ) * c, Real.sqrt a * y.2)
      = (Real.sqrt a * (y.1 - (n : ℝ) * (c / Real.sqrt a)), Real.sqrt a * y.2) := by
    congr 1
    linear_combination (n : ℝ) * key
  rw [hpt, hG]
  exact mul_inv_cancel_left₀ hne _

/-- Points of the cell `d = c/√a`, scaled by `√a`, lie in the cell `c`. -/
theorem g2fr_mem_cell_smul (c a : ℝ) (ha : 0 < a) (y : ℝ × ℝ)
    (hy : y ∈ B0579.cell (c / Real.sqrt a)) :
    (Real.sqrt a * y.1, Real.sqrt a * y.2) ∈ B0579.cell c := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have key : Real.sqrt a * (c / Real.sqrt a) = c := by
    field_simp
  have e1 : Real.sqrt a * (-((c / Real.sqrt a) / 2)) = -(c / 2) := by
    linear_combination (-1 / 2 : ℝ) * key
  have e2 : Real.sqrt a * ((c / Real.sqrt a) / 2) = c / 2 := by
    linear_combination (1 / 2 : ℝ) * key
  unfold B0579.cell at hy
  obtain ⟨⟨h1a, h1b⟩, -⟩ := hy
  unfold B0579.cell
  refine ⟨⟨?_, ?_⟩, Set.mem_univ _⟩
  · calc -(c / 2) = Real.sqrt a * (-((c / Real.sqrt a) / 2)) := e1.symm
      _ ≤ Real.sqrt a * y.1 := mul_le_mul_of_nonneg_left h1a hs.le
  · calc Real.sqrt a * y.1 < Real.sqrt a * ((c / Real.sqrt a) / 2) :=
        mul_lt_mul_of_pos_left h1b hs
      _ = c / 2 := e2

/-- Transfer of the frozen dual along `J_a⁻¹`: a.e. equality on the cell `c` gives a.e. equality of
`J_a⁻¹ f` on the cell `c/√a`, hence equal pairings. -/
theorem g2fr_frozen_transfer (κ : IIIa.PlanarFrameKernels) (c a : ℝ) (ha : 0 < a) (i : Fin 2)
    (f g : ℝ × ℝ → ℂ) (hfg : f =ᵐ[volume.restrict (B0579.cell c)] g) :
    ∫ y in B0579.cell (c / Real.sqrt a),
        IIIa.perLam κ (c / Real.sqrt a) i y * IIIa.JscaleInv a f y =
      ∫ y in B0579.cell (c / Real.sqrt a),
        IIIa.perLam κ (c / Real.sqrt a) i y * IIIa.JscaleInv a g y := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hN : volume {p : ℝ × ℝ | ¬ (p ∈ B0579.cell c → f p = g p)} = 0 :=
    ae_iff.1 ((ae_restrict_iff' (B0579.measurableSet_cell c)).1 hfg)
  have hpre : ∀ᵐ y ∂(volume : Measure (ℝ × ℝ)), y ∈ B0579.cell (c / Real.sqrt a) →
      f (Real.sqrt a * y.1, Real.sqrt a * y.2) = g (Real.sqrt a * y.1, Real.sqrt a * y.2) := by
    rw [ae_iff]
    refine measure_mono_null ?_ (by
      rw [MeasureTheory.Measure.addHaar_preimage_smul volume hs.ne', hN, mul_zero] :
        volume ((fun y : ℝ × ℝ => Real.sqrt a • y) ⁻¹'
          {p : ℝ × ℝ | ¬ (p ∈ B0579.cell c → f p = g p)}) = 0)
    intro y hy
    have hy' : ¬ (y ∈ B0579.cell (c / Real.sqrt a) →
        f (Real.sqrt a * y.1, Real.sqrt a * y.2) = g (Real.sqrt a * y.1, Real.sqrt a * y.2)) := hy
    obtain ⟨hyd, hne⟩ := not_imp.1 hy'
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    intro hQ
    exact hne (hQ (g2fr_mem_cell_smul c a ha y hyd))
  have hae : ∀ᵐ y ∂(volume : Measure (ℝ × ℝ)), y ∈ B0579.cell (c / Real.sqrt a) →
      IIIa.JscaleInv a f y = IIIa.JscaleInv a g y := by
    filter_upwards [hpre] with y hy hyd
    unfold IIIa.JscaleInv
    rw [hy hyd]
  apply integral_congr_ae
  filter_upwards [(ae_restrict_iff' (B0579.measurableSet_cell _)).2 hae] with y hy
  simp only [hy]

theorem g2FrozenReduce : UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G2.FrozenReduce := by
  unfold FrozenReduce
  intro κ ν hν t ht j f
  obtain ⟨ht0, ht1⟩ := ht
  have ht2 : t ≤ 2 / ν := le_trans ht1 (div_le_div_of_nonneg_right (by norm_num) hν.le)
  have hbAge : bandAge ν t = t := by
    unfold bandAge flatSigma
    rw [min_eq_left ht2, max_eq_right ht0]
  have hA : bandA ν t = 1 + ν * t := by
    unfold bandA IIIa.clockA
    rw [hbAge]
  have hD : bandD ν (cOf ν) t = cOf ν / Real.sqrt (1 + ν * t) := by
    unfold bandD IIIa.cellLen
    rw [hA]
  have hfE : ∀ g : ℝ × ℝ → ℂ, frozenEll κ ν (cOf ν) j t g =
      ∫ y in B0579.cell (cOf ν / Real.sqrt (1 + ν * t)),
        IIIa.perLam κ (cOf ν / Real.sqrt (1 + ν * t)) (pmIdx j) y *
          IIIa.JscaleInv (1 + ν * t) g y := by
    intro g
    unfold frozenEll
    rw [hD, hA]
  have ha : 0 < 1 + ν * t := by
    have := mul_nonneg hν.le ht0
    linarith
  have hsrc : srcA ν t = 1 + ν * t := by
    unfold srcA ageA
    rw [max_eq_left ht0]
  have hH : ∀ c : ℝ, HProf ν c t = IIIa.periodizeC c (hMode (1 + ν * t)) := by
    intro c
    unfold HProf
    rw [hsrc]
  have hR : ∀ c : ℝ, RProf ν c t = IIIa.periodizeC c (rMode (1 + ν * t)) := by
    intro c
    unfold RProf
    rw [hsrc]
  have hC : ∀ c : ℝ, (fun p => conj (HProf ν c t p)) =
      IIIa.periodizeC c (fun u => conj (hMode (1 + ν * t) u)) := by
    intro c
    funext p
    rw [hH c]
    unfold IIIa.periodizeC
    exact Complex.conj_tsum _
  have P1 : ∀ y, IIIa.JscaleInv (1 + ν * t) (HProf ν (cOf ν) t) y =
      IIIa.periodizeC (cOf ν / Real.sqrt (1 + ν * t)) (hMode 1) y := by
    intro y
    rw [hH]
    exact g2fr_jscale_periodize (1 + ν * t) (cOf ν) ha (hMode (1 + ν * t)) (hMode 1)
      (g2fr_hMode_smul (1 + ν * t) ha) y
  have P2 : ∀ y, IIIa.JscaleInv (1 + ν * t) (fun p => conj (HProf ν (cOf ν) t p)) y =
      IIIa.periodizeC (cOf ν / Real.sqrt (1 + ν * t)) (fun u => conj (hMode 1 u)) y := by
    intro y
    rw [hC]
    exact g2fr_jscale_periodize (1 + ν * t) (cOf ν) ha (fun u => conj (hMode (1 + ν * t) u))
      (fun u => conj (hMode 1 u)) (g2fr_conj_hG (1 + ν * t) ha) y
  have P3 : ∀ y, IIIa.JscaleInv (1 + ν * t) (RProf ν (cOf ν) t) y =
      IIIa.periodizeC (cOf ν / Real.sqrt (1 + ν * t)) (rMode 1) y := by
    intro y
    rw [hR]
    exact g2fr_jscale_periodize (1 + ν * t) (cOf ν) ha (rMode (1 + ν * t)) (rMode 1)
      (g2fr_rMode_smul (1 + ν * t) ha) y
  refine ⟨?_, ?_, ?_⟩
  · intro hf
    rw [hfE, g2fr_frozen_transfer κ (cOf ν) (1 + ν * t) ha (pmIdx j) f (HProf ν (cOf ν) t) hf]
    congr 1
    funext y
    rw [P1]
  · intro hf
    rw [hfE, g2fr_frozen_transfer κ (cOf ν) (1 + ν * t) ha (pmIdx j) f
      (fun p => conj (HProf ν (cOf ν) t p)) hf]
    congr 1
    funext y
    rw [P2]
  · intro hf
    rw [hfE, g2fr_frozen_transfer κ (cOf ν) (1 + ν * t) ha (pmIdx j) f (RProf ν (cOf ν) t) hf]
    congr 1
    funext y
    rw [P3]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G2
