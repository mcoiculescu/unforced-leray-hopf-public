import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Leaves

/-!
# `PartIII-b:C/flatset/col/2`: `FlatForceLocal` from three lattice-sum facts

Source of record: `the November 2 reference manuscript`, lines 4594-4596, 4988
("the sums and their required derivatives converge by Gaussian decay").
On `s ≥ s₁ > 0` the force `f_A = -Σ_j [(B_mer x_j)·∇V_j + B V_j]` is a Weierstrass `M`-test sum of
continuous terms, hence continuous on the compact box `[s₁,s₂] × [-c/2,c/2] × [-R,R]`, hence
integrable on the subset `[s₁,s₂] × (cell ∩ {|η| ≤ R})`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- **Leaf 1** (source 4957-4958): `B = (χ A)' + μ χ A / s` is continuous on `(0,∞)`.
Route: `IsAffElem.smooth` is `C^6` on the open set `(0,∞)`, `IsSourceCutoffC.smooth` gives `χ`
smooth, so `Ay ν χ A = χ(ν ·) • A` is `C^6` there and `deriv (Ay ν χ A)` is continuous
(`ContDiffOn.continuousOn_deriv_of_isOpen`); `μ / s` is continuous on `(0,∞)`. -/
def FlatBmatCont : Prop :=
  ∀ (ν μ as : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3), IsSourceCutoffC χ → IsAffElem as A →
    ContinuousOn (Bmat ν μ χ A) (Ioi 0)

/-- **Leaf 2** (source 4976): for `ν > 0`, `j ∈ ℤ` and a matrix function `B` continuous on `(0,∞)`,
the `j`-th lattice term of `-f_A` is jointly continuous in `(s, x)` on `s > 0`.
Route: `(s,x) ↦ Vj ν s j x` is `C^∞` on `{s > 0}` (explicit Gaussian formula, `ageA ν s = 1 + ν s > 0`),
so `fderiv ℝ (Vj ν s j) x` is jointly continuous (`ContDiffOn.fderiv_of_isOpen`-type results, or
the explicit formula for `fderiv`); then compose with the continuous `B`. -/
def FlatTermCont : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (j : ℤ) (B : ℝ → Mat3), ContinuousOn B (Ioi 0) →
    ContinuousOn (fun p : Chart =>
      emb (fderiv ℝ (Vj ν p.1 j) p.2 (merApply (B p.1) (xj ν j p.2)))
        + mv (B p.1) (emb (Vj ν p.1 j p.2))) (Ioi 0 ×ˢ univ)

/-- **Leaf 3** (source 4988, 4991: Gaussian decay): for `ν > 0`, `0 < s₁`, and bounds `R`, `X₀`,
`Bb` there is a summable `M : ℤ → ℝ` dominating every lattice term uniformly over
`s ∈ [s₁,s₂]`, all matrices with entries `≤ Bb`, and `|x₁| ≤ X₀`, `|x₂| ≤ R`.
Route: `Vj` and `fderiv (Vj)` are an explicit polynomial in `x_j` times `a⁻ᵏ e^{-|x_j|²/(4a)}`,
`a = 1 + ν s ∈ [1 + ν s₁, 1 + ν s₂]`; bound by `C (1+|j|)^k exp(-α (q - j c)²)` with `α = 1/(4(1+νs₂))`
(`Concrete/SummableProof.lean`: `gauss_pow_summable` is private, re-prove or copy) and
`|q| ≤ X₀`. -/
def FlatTermBound : Prop :=
  ∀ (ν s₁ s₂ R X₀ Bb : ℝ), 0 < ν → 0 < s₁ →
    ∃ M : ℤ → ℝ, Summable M ∧ ∀ s ∈ Icc s₁ s₂, ∀ B : Mat3, (∀ a b, |B a b| ≤ Bb) →
      ∀ x : ℝ × ℝ, |x.1| ≤ X₀ → |x.2| ≤ R → ∀ j : ℤ,
        ‖emb (fderiv ℝ (Vj ν s j) x (merApply B (xj ν j x))) + mv B (emb (Vj ν s j x))‖ ≤ M j

theorem flatForceLocal_of (h1 : FlatBmatCont) (h2 : FlatTermCont) (h3 : FlatTermBound) :
    FlatForceLocal := by
  intro ν μ as χ A hν hχ hA s₁ s₂ R hs₁ i
  have hc : 0 < cOf ν := by
    unfold cOf; exact inv_pos.mpr (pow_pos hν 2)
  set K : Set Chart := Icc s₁ s₂ ×ˢ (Icc (-(cOf ν / 2)) (cOf ν / 2) ×ˢ Icc (-R) R) with hK
  have hKc : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hKs : K ⊆ Ioi 0 ×ˢ univ := fun p hp =>
    ⟨lt_of_lt_of_le hs₁ hp.1.1, mem_univ _⟩
  have hBc : ContinuousOn (Bmat ν μ χ A) (Ioi 0) := h1 ν μ as χ A hχ hA
  have hBI : ContinuousOn (Bmat ν μ χ A) (Icc s₁ s₂) :=
    hBc.mono fun s hs => lt_of_lt_of_le hs₁ hs.1
  obtain ⟨Cb, hCb⟩ := isCompact_Icc.exists_bound_of_continuousOn hBI
  obtain ⟨M, hMs, hM⟩ := h3 ν s₁ s₂ R (cOf ν / 2) Cb hν hs₁
  set g : ℤ → Chart → Vec3 := fun j p =>
    emb (fderiv ℝ (Vj ν p.1 j) p.2 (merApply (Bmat ν μ χ A p.1) (xj ν j p.2)))
      + mv (Bmat ν μ χ A p.1) (emb (Vj ν p.1 j p.2)) with hg
  have hgc : ∀ j, ContinuousOn (g j) K := fun j =>
    (h2 ν hν j (Bmat ν μ χ A) hBc).mono hKs
  have hbd : ∀ (j : ℤ), ∀ p ∈ K, ‖g j p‖ ≤ M j := by
    intro j p hp
    refine hM p.1 hp.1 (Bmat ν μ χ A p.1) (fun a b => ?_) p.2 ?_ ?_ j
    · have h := ((norm_le_pi_norm ((Bmat ν μ χ A p.1) a) b).trans
        (norm_le_pi_norm ((Bmat ν μ χ A p.1)) a)).trans (hCb p.1 hp.1)
      simpa [Real.norm_eq_abs] using h
    · exact abs_le.2 ⟨hp.2.1.1, hp.2.1.2⟩
    · exact abs_le.2 ⟨hp.2.2.1, hp.2.2.2⟩
  have hsum : ContinuousOn (fun p : Chart => ∑' j, g j p) K :=
    continuousOn_tsum hgc hMs hbd
  have hcont : ContinuousOn (fun p => forceC ν μ χ A p i) K := by
    have hF : ContinuousOn (fun p : Chart => fA ν μ χ A p.1 p.2) K := hsum.neg
    have hP : Continuous (fun v : Vec3 => ((merOf v i : ℝ) : ℂ)) := by
      refine Complex.continuous_ofReal.comp ?_
      fin_cases i
      · simpa [merOf] using (continuous_apply 0).comp (continuous_id (X := Vec3))
      · simpa [merOf] using (continuous_apply 2).comp (continuous_id (X := Vec3))
    exact hP.comp_continuousOn hF
  refine (hcont.integrableOn_compact hKc).mono_set ?_
  intro p hp
  have h1 := hp.2.1.1
  have h2 := abs_le.1 (show |p.2.2| ≤ R from hp.2.2)
  exact ⟨hp.1, ⟨h1.1, h1.2.le⟩, h2⟩

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
